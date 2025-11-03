signature MRBNF_CORECURSOR =
sig
  type corecursor_result = string;

  val create_binding_corecursor: (binding -> binding) -> MRBNF_FP_Def_Sugar.fp_result
    -> local_theory -> corecursor_result * local_theory;
  val get_CORECs: string -> local_theory -> term list;

end

structure MRBNF_Corecursor : MRBNF_CORECURSOR =
struct

open MRBNF_Util

type corecursor_result = string;

fun mk_names _ [] = []
  | mk_names s [_] = [s]
  | mk_names s xs = map (fn i => s ^ string_of_int i) (1 upto length xs)

fun mk_bin_map name mk_T f g =
  let
    val f_T = fastype_of f
    val g_T = fastype_of g
    val (fa, fb) = dest_funT f_T
    val (ga, gb) = dest_funT g_T
  in Const (name, f_T --> g_T --> mk_T (fa, ga) --> mk_T (fb, gb)) $ f $ g end;

fun mk_rel_sum (L, R) =
  let
    val LT = fastype_of L;
    val RT = fastype_of R;
    val (LdomT, LrangeT) = dest_pred2T LT;
    val (RdomT, RrangeT) = dest_pred2T RT;
    val sumT = mk_pred2T (mk_sumT (LdomT, RdomT)) (mk_sumT (LrangeT, RrangeT));
  in Const (\<^const_name>\<open>rel_sum\<close>, LT --> RT --> sumT) $ L $ R end;

fun alternate l r xs ys =
  case (xs, ys) of
    ([], ys') => ys'
    | (xs', []) => xs'
    | (xs', ys') =>
        let
          val (xInit, xRest) = chop l xs';
          val (yInit, yRest) = chop r ys';
        in
          xInit @ yInit @ alternate l r xRest yRest
        end;

fun pred_True T = Term.abs ("_", T) @{term True};

fun mk_pred_sum P Q =
  let
    val PT = fastype_of P;
    val QT = fastype_of Q;
    val fT = mk_sumT (domain_type PT, domain_type QT);
  in Const (@{const_name pred_sum}, PT --> QT --> fT --> @{typ bool}) $ P $ Q end;

fun get_CORECs name lthy = map (fst o Term.dest_comb o
  fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o snd o Logic.strip_horn o Thm.prop_of
) (Proof_Context.get_thms lthy (name ^ ".COREC_dtor"))

fun create_binding_corecursor qualify fp_res no_defs_lthy =
  let
    val tvars = map TVar (rev (Term.add_tvarsT (#T (hd (#quotient_fps fp_res))) []))
      @ map TFree (rev (Term.add_tfreesT (#T (hd (#quotient_fps fp_res))) []));
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

    val (uTs, _) = Name.make_context (map (fst o dest_TFree) (vars @ plives'))
      |> apfst (map (TFree o rpair @{sort type})) o fold_map Name.variant (mk_names "'u" (replicate (length (#quotient_fps fp_res)) ()));

    val rawTs = map #T (#raw_fps fp_res);
    val qTs = map #T (#quotient_fps fp_res);
    val fTs = map (fn a => a --> a) vars;

    val bfrees = map (nth vars) (#bfree_vars fp_res)
    val bounds = pbounds @ vars;
    val frees = vars @ pfrees @ bfrees;

    fun mk_pre_Ts Ts = map2 (fn mrbnf => fn uT => uT --> HOLogic.mk_setT (MRBNF_Def.mk_T_of_mrbnf
      (MRBNF_Def.deads_of_mrbnf mrbnf) (plives @ flat (@{map 3} (fn T => fn uT => fn n =>
        replicate n (mk_sumT (T, uT))
      ) Ts uTs (#rec_vars fp_res))) bounds frees mrbnf
    )) (#pre_mrbnfs fp_res) uTs;
    val pre_Ts = mk_pre_Ts qTs;

    fun mk_raw_pre_Ts Ts = map2 (fn mrbnf => fn uT => uT --> (MRBNF_Def.mk_T_of_mrbnf
      (MRBNF_Def.deads_of_mrbnf mrbnf) (plives @ flat (@{map 3} (fn T => fn uT => fn n =>
        replicate n (mk_sumT (T, uT))
      ) Ts uTs (#rec_vars fp_res))) bounds frees mrbnf
    )) (#pre_mrbnfs fp_res) uTs;
    val raw_pre_Ts = mk_raw_pre_Ts rawTs;

    val raw_or_uTs = map2 (fn T => fn uT => mk_sumT (T, uT)) rawTs uTs;

    fun mk_un_ctor_Ts Ts = map (fn mrbnf => (MRBNF_Def.mk_T_of_mrbnf
      (MRBNF_Def.deads_of_mrbnf mrbnf) (plives @ flat (map2 (fn T => fn n =>
        replicate n T
      ) Ts (#rec_vars fp_res))) bounds frees mrbnf
    )) (#pre_mrbnfs fp_res);
    val un_ctor_Ts = mk_un_ctor_Ts rawTs;

    val ((((Umaps, UFVarsss), Udtors), validUs), names_lthy) = names_lthy
      |> mk_Frees "Umap" (map (fn uT => fTs ---> uT --> uT) uTs)
      ||>> mk_Freess "UFVars" (map (fn uT => map (fn a => uT --> HOLogic.mk_setT a) vars) uTs)
      ||>> mk_Frees "Udtor" pre_Ts
      ||>> mk_Frees "validU" (map (fn uT => uT --> @{typ bool}) uTs);

    val (((((((((((((((ds, ds'), fs), gs), Xs), Xs'), xs), picks), picks'), rawXs), rawXs') , ts), ts'), tds), un_ctors), names_lthy) = names_lthy
      |> mk_Frees "d" uTs
      ||>> mk_Frees "d'" uTs
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "g" fTs
      ||>> mk_Frees "X" (map (HOLogic.dest_setT o body_type) pre_Ts)
      ||>> mk_Frees "X'" (map (HOLogic.dest_setT o body_type) pre_Ts)
      ||>> mk_Frees "a" vars
      ||>> mk_Frees "pick" raw_pre_Ts
      ||>> mk_Frees "pick'" raw_pre_Ts
      ||>> mk_Frees "rawX" (map body_type raw_pre_Ts)
      ||>> mk_Frees "rawX'" (map body_type raw_pre_Ts)
      ||>> mk_Frees "t" rawTs
      ||>> mk_Frees "t'" rawTs
      ||>> mk_Frees "td" raw_or_uTs
      ||>> mk_Frees "x" un_ctor_Ts;
    val bfree_fs = map (nth fs) (#bfree_vars fp_res);
    val bfree_gs = map (nth gs) (#bfree_vars fp_res);

    val lthy = no_defs_lthy;

    fun replicate_rec xs = flat (map2 replicate (#rec_vars fp_res) xs);

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
    val pre_setss = mk_pre_setss (map (HOLogic.dest_setT o body_type) pre_Ts);
    val raw_pre_setss = mk_pre_setss (map body_type raw_pre_Ts);
    
    val mk_prems = maps (fn f => [mk_bij f, mk_supp_bound f]);
    val f_prems' = mk_prems fs;
    val f_prems = map HOLogic.mk_Trueprop f_prems';
    val g_prems' = mk_prems gs;
    val g_prems = map HOLogic.mk_Trueprop g_prems';
    val nvars = length vars;
    val nrecs = foldr1 (op+) (#rec_vars fp_res);

    val mk_map_sum = mk_bin_map @{const_name map_sum} BNF_Util.mk_sumT

    val reps = map (#rep o #inner) (#quotient_fps fp_res);
    val abss = map (#abs o #inner) (#quotient_fps fp_res);
    val alphas = map (#alpha o #inner) (#raw_fps fp_res);

    val binding_rel = map flat (#binding_relation fp_res);

    val rec_boundss = map (fn i =>
      @{map_filter 2} (fn j => fn rel =>
        if member (op=) rel i then SOME j else NONE
      ) (0 upto length binding_rel - 1) binding_rel
    ) (0 upto nrecs - 1);

  
    val nbfrees = map (fn i => if member (op=) (#bfree_vars fp_res) i then
      1 else 0
    ) (0 upto nvars - 1);

    val goals = @{map 14} (fn i => fn name => fn mrbnf => fn d => fn X => fn X' => fn rawX => fn Umap => fn UFVarss => fn Udtor
      => fn validU => fn (rec_sets, bsets, fsets) => fn (raw_rec_sets, raw_bsets, raw_fsets) => fn quot =>
      let
        val Udtor_ne = Logic.all d (Logic.mk_implies (
          HOLogic.mk_Trueprop (validU $ d),
          HOLogic.mk_Trueprop (
            HOLogic.mk_not (HOLogic.mk_eq (Udtor $ d, mk_bot (fastype_of X)))
          )
        ));

        val bfree_setss = map (fn i => if member (op=) (#bfree_vars fp_res) i then
          [nth (drop nvars fsets) i $ X] else []
        ) (0 upto nvars - 1);

        val fsets = take nvars fsets;

        val mk_FVarsBDs = fn FVarsss => fn bsets => fn rec_sets => fn X => @{map 5} (fn bfree_sets => fn bset => fn rel => fn FVarss => fn UFVarss =>
          mk_minus (foldl1 mk_Un (
            bfree_sets @ map_filter (fn (i, (FVars, UFVars)) => 
              if member (op=) (flat rel) i then SOME (mk_UNION (nth rec_sets i $ X)
                 (BNF_FP_Util.mk_case_sum (FVars, UFVars))
              ) else NONE
            ) ((0 upto nrecs - 1) ~~ replicate_rec (FVarss ~~ UFVarss))
          ), bset $ X)
        ) bfree_setss bsets (#binding_relation fp_res) FVarsss (transpose UFVarsss);

        val FFVarsBDs = mk_FVarsBDs (transpose (map #FVarss (#quotient_fps fp_res))) bsets rec_sets;
        val raw_UFVarsBDs = mk_FVarsBDs (transpose (map #FVarss (#raw_fps fp_res))) raw_bsets raw_rec_sets;

        val id_ons = map2 (fn f => fn fvar_union =>
          mk_id_on fvar_union f
        ) fs (FFVarsBDs X);

        val alpha_Udtor = fold_rev Logic.all [X, X', d] (fold_rev (curry Logic.mk_implies) (
          [HOLogic.mk_Trueprop (validU $ d), HOLogic.mk_Trueprop (mk_leq
            (mk_insert X (mk_insert X' (mk_bot (fastype_of X)))) (Udtor $ d)
          )]
        ) (HOLogic.mk_Trueprop (fold_rev (mk_ex o dest_Free) fs (foldr1 HOLogic.mk_conj (
          f_prems' @ id_ons @ [HOLogic.mk_eq (
            MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ @{map 3} (fn bounds => fn permute => fn Umap =>
                let val fs' = map_index (fn (i, f) => if member (op=) bounds i then f
                  else HOLogic.id_const (domain_type (fastype_of f))
                ) fs
                in if forall (fn Const (@{const_name id}, _) => true | _ => false) fs' then
                  HOLogic.id_const (mk_sumT (body_type (fastype_of permute), body_type (fastype_of Umap)))
                else mk_map_sum (Term.list_comb (permute, fs')) (Term.list_comb (Umap, fs')) end
              ) rec_boundss (replicate_rec (map #permute (#quotient_fps fp_res))) (replicate_rec Umaps))
              (map HOLogic.id_const pbounds @ fs) (map HOLogic.id_const (vars @ pfrees) @ bfree_fs) mrbnf $ X,
            X'
          )]
        )))));

        val ufvars_Udtors = @{map 5} (fn i => fn UFVars => fn fset => fn bset => fn bfrees =>
          let
            val recs = @{map 4} (fn set => fn bounds => fn FVarss => fn UFVarss =>
              let val rec_set = mk_UNION (set $ X) (
                let val filter = the o List.find (fn set => body_type (fastype_of set) = body_type (fastype_of fset))
                in BNF_FP_Util.mk_case_sum (filter FVarss, filter UFVarss) end
              ) in if member (op=) bounds i then mk_minus (rec_set, bset $ X) else rec_set end
            ) rec_sets rec_boundss (replicate_rec (map #FVarss (#quotient_fps fp_res))) (replicate_rec UFVarsss);
          in fold_rev Logic.all [d, X] (fold_rev (curry Logic.mk_implies)
            (map HOLogic.mk_Trueprop [ validU $ d, HOLogic.mk_mem (X, Udtor $ d)])
            (HOLogic.mk_Trueprop (mk_leq (foldl1 mk_Un ((fset $ X) ::
              map (fn bfree => mk_minus (bfree, bset $ X)) bfrees @ recs
            )) (UFVars $ d)))
          ) end
         ) (0 upto nvars - 1) UFVarss fsets bsets bfree_setss;

        val Umap_comp =
          let
            val Umap_comp_body_lhs = Term.list_comb (Umap ,(fs @ [Term.list_comb (Umap, (gs @ [d]))]));
            val Umap_comp_body_rhs = Term.list_comb (Umap, (map2 (curry HOLogic.mk_comp) fs gs)) $ d;
          in
            fold_rev Logic.all (fs @ gs @ [d]) (fold_rev (curry Logic.mk_implies)
              (HOLogic.mk_Trueprop (validU $ d) :: f_prems @ g_prems)
              (HOLogic.mk_Trueprop (HOLogic.mk_eq (Umap_comp_body_lhs, Umap_comp_body_rhs)))       
            )
          end

        val Umap_cong =
          let
            val Umap_cong_body_lhs = Term.list_comb (Umap, (fs @ [d]));
            val Umap_cong_body_rhs = d;
            val Ufvars_prems = @{map 3} (fn UFVars => fn f => fn a =>
              Logic.all a (Logic.mk_implies
                (HOLogic.mk_Trueprop (HOLogic.mk_mem (a, UFVars $ d)),
                  HOLogic.mk_Trueprop (HOLogic.mk_eq (f $ a, a))
                  ))) UFVarss fs xs
          in
            fold_rev Logic.all (fs @ [d]) (fold_rev (curry Logic.mk_implies)
              (HOLogic.mk_Trueprop (validU $ d) :: f_prems @ Ufvars_prems)
              (HOLogic.mk_Trueprop (HOLogic.mk_eq (Umap_cong_body_lhs, Umap_cong_body_rhs)))
            )
          end

        val valid_Umap =
          fold_rev Logic.all (fs @ [d]) (fold_rev (curry Logic.mk_implies)
            (f_prems @ [HOLogic.mk_Trueprop (validU $ d)])
            (HOLogic.mk_Trueprop (validU $ Term.list_comb (Umap, (fs @ [d]))))
          )

          val valid_Udtor =
            let
              val As = flat (@{map 3} (fn T => fn uT => fn n =>
                replicate n (mk_sumT (T, uT))
                ) qTs uTs (#rec_vars fp_res));
              fun mk_UPred validUs deads plives As bounds frees mrbnf =
              Term.list_comb (
                MRBNF_Def.mk_pred_of_mrbnf deads (plives @ As) bounds frees mrbnf,
                map pred_True plives @ map2 (fn pred => fn T =>
                  mk_pred_sum (pred_True T) pred
                  ) (replicate_rec validUs) (replicate_rec qTs)
                  );
              val uPred = mk_UPred validUs (MRBNF_Def.deads_of_mrbnf mrbnf) plives As bounds frees mrbnf
            in
              fold_rev Logic.all [d, X] (fold_rev (curry Logic.mk_implies)
                (map HOLogic.mk_Trueprop [ validU $ d, HOLogic.mk_mem (X, Udtor $ d)])
                (HOLogic.mk_Trueprop (uPred $ X))
              )
            end

        val umap_Udtor =
          let
            val map_sum_args = map2 (fn permute => fn Umap =>
                mk_map_sum (Term.list_comb (permute, fs)) (Term.list_comb (Umap, fs)))
              (replicate_rec (map #permute (#quotient_fps fp_res))) (replicate_rec Umaps);
  
            val image_arg = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ map_sum_args)
              (map HOLogic.id_const pbounds @ fs) (fs @ map HOLogic.id_const (pfrees) @ bfree_fs) mrbnf;
  
            val umap_Udtor_body_lhs = Udtor $ Term.list_comb (Umap, fs @ [d]);
            val umap_Udtor_body_rhs = mk_image image_arg $ (Udtor $ d);
            val umap_Udtor_body = mk_leq umap_Udtor_body_lhs umap_Udtor_body_rhs;
          in
            fold_rev Logic.all (fs @ [d]) (fold_rev (curry Logic.mk_implies)
              (HOLogic.mk_Trueprop (validU $ d) :: f_prems)
              (HOLogic.mk_Trueprop umap_Udtor_body)
            )
          end

      in [
        (name ^ "_ne", [Udtor_ne]),
        ("alpha_" ^ name, [alpha_Udtor]),
        ("UFVars_" ^ name, ufvars_Udtors),
        ("Umap_" ^ name, [umap_Udtor]),
        ("Umap_comp" ^ string_of_int i, [Umap_comp]),
        ("Umap_cong" ^ string_of_int i, [Umap_cong]),
        ("valid_Umap" ^ string_of_int i, [valid_Umap]),
        ("valid_" ^ name, [valid_Udtor])
      ] end
    ) (1 upto length uTs) (mk_names "Udtor" (1 upto length uTs)) (#pre_mrbnfs fp_res) ds Xs Xs' rawXs Umaps UFVarsss Udtors validUs pre_setss raw_pre_setss (#quotient_fps fp_res);

    val (corecursor_result, lthy) = Local_Theory.background_theory_result (fn thy =>
      let
        val T_names = map (short_type_name o fst o dest_Type) qTs;
        fun mk_lname s = qualify (Binding.prefix_name (s ^ "_") (Binding.conglomerate (map Binding.name T_names)));
      
        val (name, lthy) = Expression.add_locale (mk_lname "COREC") Binding.empty [] ([], []) [
          Element.Fixes (map (fn t =>
            let val (b, T) = dest_Free t;
            in (Binding.name b, SOME T, NoSyn) end
          ) (Udtors @ Umaps @ flat UFVarsss @ validUs)),
          Element.Assumes (map (fn (b, ts) => ((Binding.concealed (Binding.name b), []), map (rpair []) ts)) (
            flat goals
          ))
        ] thy;

        fun get_axioms goalss lthy = map (fn [Udtor_ne, alpha_Udtor, UFVars_Udtor, Umap_Udtor, Umap_comp, Umap_cong, valid_Umap, valid_Udtor] => {
          Udtor_ne = Proof_Context.get_thms lthy (fst Udtor_ne),
          alpha_Udtor = Proof_Context.get_thms lthy (fst alpha_Udtor),
          UFVars_Udtor = Proof_Context.get_thms lthy (fst UFVars_Udtor),
          Umap_comp = Proof_Context.get_thms lthy (fst Umap_comp),
          Umap_cong = Proof_Context.get_thms lthy (fst Umap_cong),
          valid_Umap = Proof_Context.get_thms lthy (fst valid_Umap),
          valid_Udtor = Proof_Context.get_thms lthy (fst valid_Udtor),
          Umap_Udtor = Proof_Context.get_thms lthy (fst Umap_Udtor)
        } | _ => error "impossible") goalss;

        val axiomss = get_axioms goals lthy;

        val Udtor_nes = map (hd o #Udtor_ne) axiomss;
        val alpha_Udtors = map (hd o #alpha_Udtor) axiomss;
        val UFVars_Udtorss = map #UFVars_Udtor axiomss;
        val Umap_comps = map (hd o #Umap_comp) axiomss;
        val Umap_cong_ids = map (hd o #Umap_cong) axiomss;
        val valid_Umaps = map (hd o #valid_Umap) axiomss;
        val valid_Udtors = map (hd o #valid_Udtor) axiomss;
        val Umap_Udtors = map (hd o #Umap_Udtor) axiomss;

        val permute_comp0s = (map #permute_comp0 o #quotient_fps) fp_res;
        val permute_id0s = (map #permute_id0 o #quotient_fps) fp_res;
        val abs_reps = (map (#abs_rep o #inner) o #quotient_fps) fp_res;

        val names = map (fst o dest_Free);
        val valid_prems = map2 (HOLogic.mk_Trueprop oo curry (op$)) validUs ds;

        val Umap_ids = @{map 4} (fn valid_prem => fn d => fn Umap => fn Umap_cong0 =>
          let val goal = mk_Trueprop_eq (Term.list_comb (Umap, map HOLogic.id_const vars) $ d, d)
          in Goal.prove_sorry lthy (names [d]) [valid_prem] goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt Umap_cong0,
            resolve_tac ctxt prems,
            REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound id_apply}
          ]) end
        ) valid_prems ds Umaps Umap_cong_ids;

        fun split_recs sets = fst (fold_map chop (#rec_vars fp_res) sets)

        val ((zs, rs), names_lthy) = names_lthy
          |> mk_Frees "z" (map2 (curry mk_sumT) qTs uTs)
          ||>> mk_Frees "r" uTs;

        val mrbnfs = #pre_mrbnfs fp_res;

        val (_, lthy) = Local_Theory.begin_nested lthy;

        val mk_defs_t = mk_defs_t false (Binding.conglomerate (map Binding.name T_names)) qualify

        (* Step 1: Introduce definition *)
        val (Utors, lthy) = mk_defs_t "Utor" 1 (@{map 3} (fn mrbnf => fn d => fn Udtor =>
          let
            val map_sum_args = map2 (fn rep => fn uT =>
              mk_map_sum rep (HOLogic.id_const uT))
            (replicate_rec reps) (replicate_rec uTs);
            val image_arg = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ map_sum_args)
              (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
              mrbnf;
            val body = mk_image image_arg $ (Udtor $ d);
          in
          Term.absfree (dest_Free d) body
          end
        ) mrbnfs ds Udtors) lthy;

        val (suitables, lthy) = mk_defs_t "suitable" 1
          (@{map 4} (fn pick => fn d => fn Utor => fn validU =>
            Term.absfree (dest_Free pick)
              ((mk_all o dest_Free) d (HOLogic.mk_imp
                (validU $ d, HOLogic.mk_mem (pick $ d, Utor $ d)))))
            picks ds (map fst Utors) validUs) lthy;

        val corecs = (either (fn _ => []) #corec o the o #fp_thms) fp_res;

        val (fDefns, lthy) = mk_defs_t "f" (length picks)
          (map (fn corec =>
            let
              val tyenv = Sign.typ_match
              (Proof_Context.theory_of lthy)
                (domain_type (fastype_of corec), fastype_of (hd picks)) Vartab.empty;
              val subst = Envir.subst_term (tyenv, Vartab.empty);
              val body = Term.list_comb (corec, picks);
              val body = subst body;
            in
              fold_rev (Term.absfree o dest_Free) picks body
            end) corecs) lthy;

        val (pick0s, lthy) = mk_defs_t "pick0_" 0
          (map2 (fn pick => fn suitable => HOLogic.choice_const (fastype_of pick) $
            (Term.absfree (dest_Free pick) (suitable $ pick)))
            picks (map fst suitables)) lthy;

        val (f0Defns, lthy) = mk_defs_t "f0_" 0
          (map (fn fDefn =>
            let
              val body = Term.list_comb (fDefn, (map fst pick0s));
            in
              body
            end) (map fst fDefns)) lthy;

        val (corecDefns, lthy) = mk_defs_t "COREC" 1
          (@{map 3} (fn d => fn abs => fn f0 =>
            (Term.absfree (dest_Free d) (abs $ (f0 $ d))))
            ds abss (map fst f0Defns)) lthy;

        val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
        val phi = Proof_Context.export_morphism old_lthy lthy;

        val morph =
          let
            val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (apply2 fastype_of (
              Morphism.term phi (fst (hd Utors)), (fst (hd Utors))
            )) Vartab.empty;
          in map_prod (Envir.subst_term (tyenv, Vartab.empty) o Morphism.term phi) (Morphism.thm phi) end;

        (* Step 2: Export it as constant *)
        val Utors = map morph Utors;
        val suitables = map morph suitables;
        val fDefns = map morph fDefns;
        val pick0s = map morph pick0s;
        val f0Defns = map morph f0Defns;
        val corecDefns = map morph corecDefns;

        fun mk_setr x =
          let val T = fastype_of x;
          in Const (@{const_name Basic_BNFs.setr}, T --> HOLogic.mk_setT (snd (BNF_FP_Util.dest_sumT T))) $ x end

        val valid_Udtor' = @{map 7} (fn mrbnf => fn valid_Udtor => fn d => fn x => fn Udtor => fn valid_U => fn (rec_sets, _, _) =>
          @{map 4} (fn inner_valid => fn rec_sets => fn z => fn r =>
            let
              val goal = fold_rev Logic.all [x, z, r] (fold_rev (curry Logic.mk_implies) (map HOLogic.mk_Trueprop [
                valid_U $ d, HOLogic.mk_mem (x, Udtor $ d), HOLogic.mk_mem (z, foldl1 mk_Un (map (fn s => s $ x) rec_sets)),
                HOLogic.mk_mem (r, mk_setr z)
              ]) (HOLogic.mk_Trueprop (inner_valid $ r)));
            in Goal.prove_sorry lthy (names [d]) [] goal (fn {context=ctxt, ...} => EVERY1 [
              dtac ctxt valid_Udtor,
              assume_tac ctxt,
              TRY o etac ctxt UnE,
              K (Local_Defs.unfold0_tac ctxt (@{thms sum.pred_set} @ [MRBNF_Def.pred_set_of_mrbnf mrbnf])),
              REPEAT_DETERM o EVERY' [
                REPEAT_DETERM o etac ctxt conjE,
                rotate_tac 2,
                dtac ctxt @{thm bspec[rotated]},
                assume_tac ctxt,
                etac ctxt conjE,
                etac ctxt bspec,
                assume_tac ctxt
              ]
            ]) end
          ) validUs (split_recs rec_sets) zs rs
        ) mrbnfs valid_Udtors ds Xs Udtors validUs pre_setss;

        val mk_FVarsBDs = fn FVarsss => fn (rec_sets, bsets, fsets) => fn X =>
          let
            val bfree_setss = map (fn i => if member (op=) (#bfree_vars fp_res) i then
              [nth (drop nvars fsets) i $ X] else []
              ) (0 upto nvars - 1);

            val fsets = take nvars fsets;
          in
            @{map 5} (fn bfree_sets => fn bset => fn rel => fn FVarss => fn UFVarss =>

            mk_minus (foldl1 mk_Un (
              bfree_sets @ map_filter (fn (i, (FVars, UFVars)) => 
                if member (op=) (flat rel) i then SOME (mk_UNION (nth rec_sets i $ X)
                   (BNF_FP_Util.mk_case_sum (FVars, UFVars))
                ) else NONE
              ) ((0 upto nrecs - 1) ~~ replicate_rec (FVarss ~~ UFVarss))
            ), bset $ X)) bfree_setss bsets (#binding_relation fp_res) FVarsss (transpose UFVarsss)
          end;
          
        val FVars_raw_defs2 = @{map 3} (fn rep_abs => map2 (fn thm => fn alpha_FVars => @{thm trans[OF meta_eq_to_obj_eq]} OF [thm,
          alpha_FVars OF [rep_abs]
        ] RS sym)) (map (#rep_abs o #inner) (#quotient_fps fp_res)) (map (#FVars_defs o #inner) (#quotient_fps fp_res)) (map (#alpha_FVarss o #inner) (#raw_fps fp_res));

        val FVarsBD_FFVarsBDs = @{map 4} (fn mrbnf => fn rawX => fn raw_pre_sets => fn pre_sets =>
          let
            val mk_FFVarsBDs = mk_FVarsBDs (transpose (map #FVarss (#quotient_fps fp_res))) pre_sets;
            val raw_UFVarsBDs = mk_FVarsBDs (transpose (map #FVarss (#raw_fps fp_res))) raw_pre_sets rawX;
            val map_sum_args = map2 (fn abs => fn uT =>
              mk_map_sum abs (HOLogic.id_const uT))
              (replicate_rec abss) (replicate_rec uTs);
            val map_fun = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ map_sum_args)
              (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
              mrbnf;
            val rhss = mk_FFVarsBDs (map_fun $ rawX);
          in
            map2 (fn raw_UFVarsBD => fn rhs =>
              let
                val goal = mk_Trueprop_eq (raw_UFVarsBD, rhs)
              in Goal.prove_sorry lthy (names [rawX]) [] goal (fn {context=ctxt, prems} => EVERY1 [
                K (Local_Defs.unfold_tac ctxt (flat FVars_raw_defs2)),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound}
                ],
                REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms image_id}),
                REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms image_image}),
                REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms case_sum_map_sum}),
                REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms comp_id}),
                REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms comp_def}),
                rtac ctxt refl
              ])
              end
            ) raw_UFVarsBDs rhss
          end
        ) mrbnfs rawXs raw_pre_setss pre_setss;

        val Umap_invs = @{map 5} (fn valid_prem => fn d => fn Umap => fn Umap_comp => fn Umap_id =>
          let
            val goal = mk_Trueprop_eq
                  ( Term.list_comb (Umap, (map mk_inv fs)
                                          @ [Term.list_comb (Umap, fs @ [d])])
                  , d
                  );
            val prems = f_prems @ [valid_prem];
          in Goal.prove_sorry lthy (names (fs @ [d])) prems goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt (trans OF [Umap_comp]),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
              resolve_tac ctxt prems
            ],
            rtac ctxt (trans OF [Umap_id]),
            resolve_tac ctxt prems,
            rtac ctxt refl
          ]) end
        ) valid_prems ds Umaps Umap_comps Umap_ids;

        val Umap_Udtor_strong = @{map 10} (fn mrbnf => fn valid_prem => fn d => fn Udtor =>
                                          fn Umap => fn Umap_Udtor => fn Umap_inv => fn valid_Umap =>
                                          fn Umap_id => fn valid_Udtor'' =>
          let
            val lhs = Udtor $ Term.list_comb (Umap, fs @ [d]);
            val map_sum_args = map2 (fn permute => fn Umap =>
                mk_map_sum (Term.list_comb (permute, fs)) (Term.list_comb (Umap, fs)))
              (replicate_rec (map #permute (#quotient_fps fp_res))) (replicate_rec Umaps);
  
            val image_arg = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ map_sum_args)
              (map HOLogic.id_const pbounds @ fs) (fs @ map HOLogic.id_const (pfrees) @ bfree_fs) mrbnf;
  
            val rhs = mk_image image_arg $ (Udtor $ d);
            val goal = mk_Trueprop_eq (lhs, rhs);
            val prems = f_prems @ [valid_prem];
          in Goal.prove_sorry lthy (names (fs @ [d])) prems goal (fn {context=ctxt, prems} =>
               let
                 val (f_prems, valid_prem) = prems
                      |> chop (length f_prems);
               in EVERY1 ([  
                 rtac ctxt @{thm subset_antisym},
                 rtac ctxt (Umap_Udtor OF (valid_prem @ f_prems)),
                 EqSubst.eqsubst_tac ctxt [0] [Umap_inv RS sym OF prems],
                 rtac ctxt @{thm image_subsetI},
                 dtac ctxt (Drule.rotate_prems ~1 (Umap_Udtor RS subsetD)),
                 REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ valid_Umap :: prems),
                 etac ctxt imageE,
                 hyp_subst_tac ctxt,
                 rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]]},
                 rtac ctxt (MRBNF_Def.map_comp_of_mrbnf mrbnf),
                 REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound supp_id_bound} @  prems),
                 K (Local_Defs.unfold0_tac ctxt @{thms map_sum.comp}),
                 REPEAT_DETERM o EVERY' [
                   EqSubst.eqsubst_tac ctxt [0] (@{thm inv_o_simp2} :: permute_comp0s),
                   REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems)
                 ],
                 TRY o (K (Local_Defs.unfold0_tac ctxt @{thms comp_id})),
                 K (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
                 K (Local_Defs.unfold0_tac ctxt (@{thm map_sum.id} :: Umap_id :: permute_id0s)),
                 rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]]},
                 rtac ctxt (Drule.rotate_prems (~nrecs) (MRBNF_Def.map_cong_of_mrbnf mrbnf)),
                 EVERY' (map2 (fn valid_Udtor' => fn Umap => EVERY' [
                   rtac ctxt @{thm sum.map_cong0[OF refl]},
                   dtac ctxt (Drule.rotate_prems 1 valid_Udtor'),
                   eresolve_tac ctxt @{thms UnI2 UnI1},
                   assume_tac ctxt,
                   rtac ctxt valid_Umap,
                   REPEAT_DETERM o (resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems) ORELSE' assume_tac ctxt),
                   rtac ctxt trans,
                   resolve_tac ctxt Umap_comps,
                   REPEAT_DETERM o (resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems) ORELSE' assume_tac ctxt),
                   rtac ctxt trans,
                   rtac ctxt (mk_arg_cong lthy (nvars + 1) Umap OF (replicate nvars @{thm _} @ [refl])),
                   REPEAT_DETERM o EVERY' [
                     rtac ctxt @{thm inv_o_simp2},
                     resolve_tac ctxt prems
                   ],
                   resolve_tac ctxt Umap_ids,
                   assume_tac ctxt
                 ]) (replicate_rec valid_Udtor'') (replicate_rec Umaps)),
                 REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id refl})),
                 K (Local_Defs.unfold0_tac ctxt (MRBNF_Def.map_id_of_mrbnf mrbnf :: permute_id0s @ Umap_ids @ @{thms map_sum.id id_def[symmetric]})),
                 assume_tac ctxt
               ])
             end
           ) end
        ) mrbnfs valid_prems ds Udtors Umaps Umap_Udtors Umap_invs valid_Umaps Umap_ids valid_Udtor';

       val abs_rep_ids = map2 (fn abs => fn rep =>
          let
            val lhs = HOLogic.mk_comp (abs, rep);
            val goal = mk_Trueprop_eq (lhs, HOLogic.id_const (domain_type (fastype_of lhs)));
          in Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, prems} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
            K (Local_Defs.unfold0_tac ctxt abs_reps),
            K (Local_Defs.fold_tac ctxt @{thms id_def}),
            rtac ctxt refl
          ]) end
        ) abss reps;

       val permute_abss = map (#permute_abs o #inner) (#quotient_fps fp_res);
       val total_abs_eq_iffs = map (#total_abs_eq_iff o #inner) (#quotient_fps fp_res);

       val DTOR_mapD = @{map 8} (fn mrbnf => fn rawX => fn rawX' => fn raw_pre_sets => fn Utor =>
                                 fn d => fn valid_prem => fn alpha_Udtor =>
         let
           val raw_UFVarsBDs = mk_FVarsBDs (transpose (map #FVarss (#raw_fps fp_res))) raw_pre_sets rawX;
           val id_ons = map2 (fn f => fn fvar_union =>
             mk_id_on fvar_union f
           ) fs raw_UFVarsBDs;

           fun mk_mr_rel deads mrbnf =
             let
               val live_Ts = plives @ replicate_rec (map2 (fn uT => fn T => (mk_sumT (T, uT))) uTs rawTs);
             in
               MRBNF_Def.mk_mr_rel_of_mrbnf deads live_Ts live_Ts (pbounds @ vars) (vars @ pfrees @ bfrees) mrbnf  
           end;

           val rel_sums = @{map 9} (fn rec_bounds => fn alpha => fn t => fn t' => fn d => fn d' => fn uT => fn raw_permute => fn Umap =>
             if null rec_bounds then
               mk_rel_sum (alpha, (HOLogic.eq_const uT))
             else let
               val fs' = map_index (fn (i, f) => if member (op=) rec_bounds i then f
                     else HOLogic.id_const (domain_type (fastype_of f))
                   ) fs
  
               val (tName, tT) = dest_Free t;
               val (tName', tT') = dest_Free t';
               val L = Abs (tName, tT, Abs (tName', tT',
                 Term.list_comb (alpha, [Term.list_comb (raw_permute, fs' @ [Bound 1]), Bound 0])));
              
               val (dName, dT) = dest_Free d;
               val (dName', dT') = dest_Free d';
               val R = Abs (dName, dT, Abs (dName', dT',
                 HOLogic.mk_eq
                   ( Term.list_comb (Umap, fs' @ [Bound 1])
                   , Bound 0
                   )));
             in
               mk_rel_sum (L, R)
             end
           ) rec_boundss (replicate_rec alphas) (replicate_rec ts) (replicate_rec ts')
             (replicate_rec ds) (replicate_rec ds') (replicate_rec uTs)
             (replicate_rec (map #permute (#raw_fps fp_res))) (replicate_rec Umaps);

           val lives = map HOLogic.eq_const plives @ rel_sums;
           val bounds' = map HOLogic.id_const pbounds @ fs;
           val frees' = map HOLogic.id_const (vars @ pfrees) @ bfree_fs;

           val mr_rel_term = Term.list_comb (
               mk_mr_rel (MRBNF_Def.deads_of_mrbnf mrbnf) mrbnf,
               MRBNF_Def.interlace lives bounds' frees' (MRBNF_Def.var_types_of_mrbnf mrbnf)
             ) $ rawX $ rawX';

           val Utor_prem = HOLogic.mk_Trueprop (mk_leq
               (mk_insert rawX (mk_insert rawX' (mk_bot (fastype_of rawX)))) (fst Utor $ d));

           val goal = Logic.mk_implies
                 ( Utor_prem
                 , HOLogic.mk_Trueprop (fold_rev (mk_ex o dest_Free) fs
                     (foldr1 HOLogic.mk_conj (alternate 2 1 f_prems' id_ons @ [mr_rel_term])))
                 );

           (* used in image_mono instantiation in the proof *)
           val map_sum_args = map2 (fn abs => fn uT =>
             mk_map_sum abs (HOLogic.id_const uT))
             (replicate_rec abss) (replicate_rec uTs);
           val map_fun = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
             (map HOLogic.id_const plives @ map_sum_args)
             (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
             mrbnf;

           val nargs = MRBNF_Def.live_of_mrbnf mrbnf + MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf;

         in Goal.prove_sorry lthy (names [d, rawX, rawX']) [valid_prem] goal (fn {context=ctxt, prems} => EVERY1 [
           dtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy map_fun)] @{thm image_mono}),
           K (Local_Defs.unfold0_tac ctxt (snd Utor :: @{thms image_insert image_empty image_comp})),
           EVERY' [
             EqSubst.eqsubst_asm_tac ctxt [0] [MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym],
             REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}))
           ],
           K (Local_Defs.unfold0_tac ctxt (MRBNF_Def.map_id0_of_mrbnf mrbnf :: abs_rep_ids @ @{thms id_o map_sum.comp map_sum.id image_id})),
           dtac ctxt (alpha_Udtor OF prems),
           REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
           REPEAT_DETERM o EVERY' [
             EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.map_comp_of_mrbnf mrbnf :: MRBNF_Def.set_map_of_mrbnf mrbnf),
             REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}) ORELSE' assume_tac ctxt)
           ],
           K (Local_Defs.unfold0_tac ctxt @{thms image_id id_o o_id map_sum.comp}),
           dtac ctxt (MRBNF_Def.mr_rel_eq_of_mrbnf mrbnf RS fun_cong RS fun_cong RS iffD2),
           EVERY' [
             EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf),
             REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}) ORELSE' assume_tac ctxt)
           ],
           K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
           EVERY' [
             EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf),
             REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}) ORELSE' assume_tac ctxt)
           ],
           K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id inv_id relcompp_conversep_Grp Grp_OO}),
           REPEAT_DETERM o rtac ctxt exI,
           REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
           etac ctxt (Drule.rotate_prems (~(nargs + 1)) (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf)),
           TRY o (K (Local_Defs.unfold0_tac ctxt [id_apply])),
           REPEAT_DETERM o EVERY' [
             rtac ctxt ballI,
             rtac ctxt refl ORELSE' EVERY' [
               rtac ctxt ballI,
               rtac ctxt @{thm imp_refl}
             ]
           ],
           REPEAT_DETERM o EVERY' [
             REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
             dtac ctxt @{thm sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2]},
             SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms sum.rel_map comp_def id_apply}),
             etac ctxt @{thm sum.rel_mono_strong},
             TRY o EVERY' [
               EqSubst.eqsubst_asm_tac ctxt [0] permute_abss,
               REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}) ORELSE' assume_tac ctxt)
             ],
             eresolve_tac ctxt (map (fn thm => thm RS iffD1) total_abs_eq_iffs),
             assume_tac ctxt
           ],
           REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}) ORELSE' assume_tac ctxt),
           K (Local_Defs.unfold_tac ctxt (flat FVars_raw_defs2 @ @{thms image_comp[unfolded comp_def] case_sum_map_sum o_id})),
           K (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
           REPEAT_DETERM o assume_tac ctxt
         ]) end
       ) mrbnfs rawXs rawXs' raw_pre_setss Utors ds valid_prems alpha_Udtors;

       val Utor_ne = @{map 3} (fn valid_prem => fn d => fn Utor =>
          let
            val lhs = fst Utor $ d;
            val setT = HOLogic.dest_setT (fastype_of lhs);
            val goal = Logic.mk_implies
              ( valid_prem
              , HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (lhs, mk_bot setT)))
              );
          in Goal.prove_sorry lthy (names [d]) [] goal (fn {context=ctxt, prems} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt (snd Utor :: @{thms arg_cong[OF image_is_empty, of Not]})),
            eresolve_tac ctxt Udtor_nes
          ]) end
        ) valid_prems ds Utors;

       val Utor_abs_Udtor = @{map 5} (fn rawX => fn d => fn Utor => fn Udtor => fn mrbnf =>
          let
            val map_sum_args = map2 (fn abs => fn uT =>
              mk_map_sum abs (HOLogic.id_const uT))
              (replicate_rec abss) (replicate_rec uTs);
            val map_fun = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ map_sum_args)
              (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
              mrbnf;

            val goal = Logic.mk_implies
              ( HOLogic.mk_Trueprop (HOLogic.mk_mem (rawX, fst Utor $ d))
              , HOLogic.mk_Trueprop (HOLogic.mk_mem (map_fun $ rawX, Udtor $ d))
              );
          in Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, prems} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt [snd Utor]),
            etac ctxt imageE,
            hyp_subst_tac_thin true ctxt,
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
            REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms map_sum.comp},
            REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms id_o},
            REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] abs_rep_ids,
            REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms map_sum.id},
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_id_of_mrbnf mrbnf],
            assume_tac ctxt
          ]) end
        ) rawXs ds Utors Udtors mrbnfs;
      
        val raw_UFVars_Utor = @{map 9} (fn mrbnf => fn UFVarss => fn rawX => fn d => fn (rec_sets, bsets, fsets) =>
                                        fn Utor => fn valid_prem => fn UFVars_Udtors => fn Utor_abs_Udtor' =>
          let
          val bfree_setss = map (fn i => if member (op=) (#bfree_vars fp_res) i then
            [nth (drop nvars fsets) i $ rawX] else []
          ) (0 upto nvars - 1);

          val fsets = take nvars fsets;
          val goals = @{map 5} (fn i => fn UFVars => fn fset => fn bset => fn bfrees =>
            let
              val recs = @{map 4} (fn set => fn bounds => fn FVarss => fn UFVarss =>
                let val rec_set = mk_UNION (set $ rawX) (
                  let val filter = the o List.find (fn set => body_type (fastype_of set) = body_type (fastype_of fset))
                  in BNF_FP_Util.mk_case_sum (filter FVarss, filter UFVarss) end
                ) in if member (op=) bounds i then mk_minus (rec_set, bset $ rawX) else rec_set end
              ) rec_sets rec_boundss (replicate_rec (map #FVarss (#raw_fps fp_res))) (replicate_rec UFVarsss);
            in Logic.mk_implies
                ( HOLogic.mk_Trueprop (HOLogic.mk_mem (rawX, Utor $ d))
                , HOLogic.mk_Trueprop (mk_leq (foldl1 mk_Un ((fset $ rawX) ::
                    map (fn bfree => mk_minus (bfree, bset $ rawX)) bfrees @ recs)) (UFVars $ d))
                )
             end
           ) (0 upto nvars - 1) UFVarss fsets bsets bfree_setss
          in map2 (fn goal => fn UFVars_Udtor =>
            Goal.prove_sorry lthy (names [rawX, d]) [valid_prem] goal (fn {context=ctxt, prems} => EVERY1 [
            dtac ctxt (UFVars_Udtor OF (prems @ [Utor_abs_Udtor'])),
            REPEAT_DETERM o EVERY' [
             EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
             REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}))
            ],
            K (Local_Defs.unfold_tac ctxt (flat FVars_raw_defs2 @ @{thms image_comp case_sum_o_map_sum o_id image_id})),
            K (Local_Defs.unfold0_tac ctxt (flat FVarsBD_FFVarsBDs @ @{thms comp_def})),
            assume_tac ctxt
          ])) goals UFVars_Udtors
          end) mrbnfs UFVarsss rawXs ds raw_pre_setss (map fst Utors) valid_prems UFVars_Udtorss Utor_abs_Udtor;

       val raw_Umap_Utor = @{map 8} (fn mrbnf => fn rawX => fn rawX' => fn Utor =>
                                 fn d => fn valid_prem => fn Umap => fn Umap_Udtor_strong' =>
         let
           fun mk_mr_rel deads mrbnf =
             let
               val live_Ts = plives @ replicate_rec (map2 (fn uT => fn T => (mk_sumT (T, uT))) uTs rawTs);
             in
               MRBNF_Def.mk_mr_rel_of_mrbnf deads live_Ts live_Ts (pbounds @ vars) (vars @ pfrees @ bfrees) mrbnf  
           end;

           val rel_sums = @{map 7} (fn alpha => fn t => fn t' => fn d => fn d' => fn raw_permute => fn Umap =>
             let
               val (tName, tT) = dest_Free t;
               val (tName', tT') = dest_Free t';
               val L = Abs (tName, tT, Abs (tName', tT',
                 Term.list_comb (alpha, [Term.list_comb (raw_permute, fs @ [Bound 1]), Bound 0])));
              
               val (dName, dT) = dest_Free d;
               val (dName', dT') = dest_Free d';
               val R = Abs (dName, dT, Abs (dName', dT',
                 HOLogic.mk_eq
                   ( Term.list_comb (Umap, fs @ [Bound 1])
                   , Bound 0
                   )));
             in
               mk_rel_sum (L, R)
             end
           ) (replicate_rec alphas) (replicate_rec ts) (replicate_rec ts')
             (replicate_rec ds) (replicate_rec ds')
             (replicate_rec (map #permute (#raw_fps fp_res))) (replicate_rec Umaps);

           val lives = map HOLogic.eq_const plives @ rel_sums;
           val bounds' = map HOLogic.id_const pbounds @ fs;
           val frees' = fs @ map HOLogic.id_const pfrees @ bfree_fs @ bfree_fs;

           val mr_rel = Term.list_comb (
               mk_mr_rel (MRBNF_Def.deads_of_mrbnf mrbnf) mrbnf,
               MRBNF_Def.interlace lives bounds' frees' (MRBNF_Def.var_types_of_mrbnf mrbnf)
             );

           val relL = fst Utor $ d;
           val relR = fst Utor $ Term.list_comb (Umap, (fs @ [d]));

            fun mk_rel_set R =
              let
                val (A::B::_) = fastype_of R |> binder_types;
              in
                MRBNF_Def.mk_rel 1 0 0 [A] [B] @{term rel_set} $ R
              end;

           val goal = HOLogic.mk_Trueprop (Term.list_comb (mk_rel_set mr_rel, [relL, relR]));

           val prems = f_prems @ [valid_prem];
         in Goal.prove_sorry lthy (names (fs @ [d, rawX, rawX'])) prems goal (fn {context=ctxt, prems} => EVERY1 [
           K (Local_Defs.unfold0_tac ctxt [snd Utor]),
           EqSubst.eqsubst_tac ctxt [0] [Umap_Udtor_strong' OF (take (length f_prems) prems)],
           resolve_tac ctxt prems,
           EqSubst.eqsubst_tac ctxt [0] @{thms image_comp},
           EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym],
           REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
           REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms map_sum.comp},
           REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms id_o},
           REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms rel_set_image},
           rtac ctxt @{thm rel_set_reflI},
           EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf),
           REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
           REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms o_id},
           REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) ORELSE' resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id})),
           REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1} ORELSE' resolve_tac ctxt (prems @ @{thms bij_id})),
           K (Local_Defs.unfold0_tac ctxt ((MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym) :: @{thms relcompp_conversep_Grp Grp_OO})),
           REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms sum.rel_map},
           K (Local_Defs.unfold_tac ctxt (map (#permute_def o #inner) (#quotient_fps fp_res))),
           rtac ctxt (MRBNF_Def.rel_refl_of_mrbnf mrbnf),
           REPEAT_DETERM o rtac ctxt refl,
           REPEAT_DETERM o EVERY' [
             rtac ctxt @{thm sum.rel_refl},
             EqSubst.eqsubst_tac ctxt [0] @{thms comp_apply},
             resolve_tac ctxt (map (#rep_abs_sym o #inner) (#quotient_fps fp_res)),
             EqSubst.eqsubst_tac ctxt [0] @{thms id_apply},
             rtac ctxt refl
           ]
         ]) end
       ) mrbnfs rawXs rawXs' Utors ds valid_prems Umaps Umap_Udtor_strong;

       val corecThms = (either (fn _ => []) #corec_def o the o #fp_thms) fp_res;
       val coinductThm = ((either (fn _ => error "impossible") #coinduct o the o #fp_thms) fp_res);

       val f_simps = @{map 6} (fn d => fn mrbnf => fn fFun => fn raw_ctor => fn pick => fn corec =>
          let
            val case_sum_args = map2 (fn rawT => fn f =>
              BNF_FP_Util.mk_case_sum ((HOLogic.id_const rawT), (Term.list_comb (f, picks))))
              (replicate_rec rawTs) (replicate_rec (map fst fDefns));
            val case_fun = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ case_sum_args)
              (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
              mrbnf;

            val goal = mk_Trueprop_eq
              ( Term.list_comb (fst fFun, picks @ [d])
              , raw_ctor $ (case_fun $ (pick $ d))
              );

          in Goal.prove_sorry lthy (names (picks @ [d])) [] goal (fn {context=ctxt, prems} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt [snd fFun]),
            EqSubst.eqsubst_tac ctxt [0] [corec],
            K (Local_Defs.fold_tac ctxt (map snd fDefns)),
            K (Local_Defs.unfold0_tac ctxt @{thms id_def}),
            rtac ctxt refl
          ]) end
        )  ds mrbnfs fDefns (map #ctor (#raw_fps fp_res)) picks corecThms;

        val f_ctor = @{map 8} (fn d => fn mrbnf => fn fFun => fn raw_ctor => fn pick => fn un_ctor => fn f_simp => fn inject =>
          let
            val case_sum_args = map2 (fn rawT => fn f =>
              BNF_FP_Util.mk_case_sum ((HOLogic.id_const rawT), (Term.list_comb (f, picks))))
              (replicate_rec rawTs) (replicate_rec (map fst fDefns));
            val case_fun = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ case_sum_args)
              (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
              mrbnf;

            val assm = mk_Trueprop_eq (raw_ctor $ un_ctor, Term.list_comb (fst fFun, picks @ [d]));

            val goal = mk_Trueprop_eq
              ( un_ctor
              , case_fun $ (pick $ d)
              );

          in Goal.prove_sorry lthy (names (picks @ [d, un_ctor])) [assm] goal (fn {context=ctxt, prems} => EVERY1 [
              rtac ctxt (Local_Defs.unfold0 lthy [inject] (trans OF (prems @ [f_simp])))
          ]) end
        )  ds mrbnfs fDefns (map #ctor (#raw_fps fp_res)) picks un_ctors f_simps (map #inject (#raw_fps fp_res));

        val suitable_FVarsD = @{map 8} (fn UFVarss => fn d => fn (rec_sets, bsets, fsets) =>
                                        fn valid_prem => fn UFVars_Udtors => fn pick => fn suitable =>
                                        fn raw_UFVars_Utor' =>
          let
          val pickd = pick $ d;
          val bfree_setss = map (fn i => if member (op=) (#bfree_vars fp_res) i then
            [nth (drop nvars fsets) i $ pickd] else []
          ) (0 upto nvars - 1);

          val fsets = take nvars fsets;
          val goals = @{map 5} (fn i => fn UFVars => fn fset => fn bset => fn bfrees =>
            let
              val recs = @{map 4} (fn set => fn bounds => fn FVarss => fn UFVarss =>
                let val rec_set = mk_UNION (set $ pickd) (
                  let val filter = the o List.find (fn set => body_type (fastype_of set) = body_type (fastype_of fset))
                  in BNF_FP_Util.mk_case_sum (filter FVarss, filter UFVarss) end
                ) in if member (op=) bounds i then mk_minus (rec_set, bset $ pickd) else rec_set end
              ) rec_sets rec_boundss (replicate_rec (map #FVarss (#raw_fps fp_res))) (replicate_rec UFVarsss);
            in 
              HOLogic.mk_Trueprop (mk_leq (foldl1 mk_Un ((fset $ pickd) ::
                map (fn bfree => mk_minus (bfree, bset $ pickd)) bfrees @ recs)) (UFVars $ d))
             end
           ) (0 upto nvars - 1) UFVarss fsets bsets bfree_setss

           val suitable_prem = HOLogic.mk_Trueprop (fst suitable $ pick);
           val prems = [suitable_prem, valid_prem];

          in map2 (fn goal => fn UFVars_Udtor =>
            Goal.prove_sorry lthy (names [pick, d]) prems goal (fn {context=ctxt, prems as (suitable_prem :: valid_prem ::  _)} =>
              let
                val sndOFarg' = Local_Defs.unfold0 lthy [snd suitable] suitable_prem;
                val sndOFarg = sndOFarg' RS spec RS mp OF [valid_prem];
                val theRule = map (fn t => t OF [valid_prem, sndOFarg]) raw_UFVars_Utor';
              in EVERY1 [
                resolve_tac ctxt theRule
          ] end)) goals UFVars_Udtors
          end) UFVarsss ds raw_pre_setss valid_prems UFVars_Udtorss picks suitables raw_UFVars_Utor;

        val is_freess = (either (fn _ => []) #is_frees o the o #fp_thms) fp_res;
        val is_free_inducts = (either (fn _ => []) #is_free_induct o the o #fp_thms) fp_res;
        val FVars_raw_defss  = (either (fn _ => []) #FVars_raw_defs o the o #fp_thms) fp_res;

        val f_FVarsD_aux = @{map 9} (fn d => fn t => fn td => fn fFun => fn FVarss =>
                                     fn FVars_raw_defs => fn UFVarss => fn validU => fn is_frees =>
          let
            val goals = @{map 3} (fn FVars => fn UFVars => fn is_free =>
              let
                val filter = the o List.find (fn var => fastype_of var = HOLogic.dest_setT (body_type (fastype_of UFVars)))
                val a = filter xs;

                val assms1 = HOLogic.mk_Trueprop (is_free $ a $ t);
    
                val assms2 = Logic.all d (fold_rev (curry Logic.mk_implies)
                  (map HOLogic.mk_Trueprop [validU $ d, HOLogic.mk_eq (t, (Term.list_comb (fst fFun, picks)) $ d)])
                  (HOLogic.mk_Trueprop (HOLogic.mk_mem (a, UFVars $ d))));
    
                val assms3 = HOLogic.mk_Trueprop (mk_pred_sum (pred_True (fastype_of t)) validU $ td);
    
                val assms = [assms1, assms2, assms3];
    
                val assm = mk_Trueprop_eq
                  ( t
                  , BNF_FP_Util.mk_case_sum ((HOLogic.id_const (fastype_of t)), (Term.list_comb (fst fFun, picks))) $ td
                  );
                
                val goal = HOLogic.mk_Trueprop (HOLogic.mk_mem (filter xs, BNF_FP_Util.mk_case_sum (FVars, UFVars) $ td));
              in
                (a, assms, Logic.mk_implies (assm, goal))
              end)
              FVarss UFVarss is_frees;

          in map (fn (a, assms, goal) => Goal.prove_sorry lthy (names (picks @ [a, t, td])) assms goal (fn {context=ctxt, prems as (is_free_prem :: prem2 :: pred_sum_prem :: _)} => EVERY1 [
              rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of lthy td)] @{thm sumE}),
              hyp_subst_tac ctxt,
              EqSubst.eqsubst_tac ctxt [0] @{thms sum.case},
              K (Local_Defs.unfold0_tac ctxt (@{thm mem_Collect_eq} :: FVars_raw_defs)),
              Method.insert_tac ctxt [is_free_prem],
              hyp_subst_tac_thin true ctxt,
              EqSubst.eqsubst_asm_tac ctxt [0] @{thms sum.case},
              EqSubst.eqsubst_asm_tac ctxt [0] [id_apply],
              assume_tac ctxt,
              hyp_subst_tac ctxt,
              EqSubst.eqsubst_tac ctxt [0] @{thms sum.case},
              rtac ctxt prem2,
              K (Local_Defs.unfold0_tac ctxt @{thms sum.simps}),
              Method.insert_tac ctxt [pred_sum_prem],
              hyp_subst_tac_thin true ctxt,
              EqSubst.eqsubst_asm_tac ctxt [0] @{thms pred_sum_inject},
              assume_tac ctxt,
              assume_tac ctxt
          ])) goals end
        )  ds ts tds  fDefns (map #FVarss (#raw_fps fp_res)) FVars_raw_defss UFVarsss validUs (transpose is_freess);

        val valid_pick_set = @{map 8} (fn mrbnf => fn d => fn r => fn valid_U => fn pick =>
                                       fn suitable => fn Utor => fn (rec_sets, _, _) =>
          @{map 4} (fn inner_valid => fn rec_sets => fn td => fn rawT =>
            let
            val goals = map (fn rec_set =>
              let val set_prem = HOLogic.mk_mem (td, rec_set $ (pick $ r));
                  val valid_prem = valid_U $ r;
                  val suitable_prem = fst suitable $ pick;
                  val res = HOLogic.mk_Trueprop (mk_pred_sum (pred_True rawT) inner_valid $ td);
               in fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop)
                    [suitable_prem, set_prem, valid_prem] res
               end
              ) rec_sets
            in map (fn goal => Goal.prove_sorry lthy (names [pick, td, r, d]) [] goal (fn {context=ctxt, ...} => EVERY1 [
              K (Local_Defs.unfold0_tac ctxt [snd suitable, snd Utor]),
              etac ctxt allE,
              etac ctxt impE,
              assume_tac ctxt,
              etac ctxt imageE,
              dtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<in>)", THEN iffD1, rotated -1]},
              etac ctxt arg_cong,
              EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}))
              ],
              rtac ctxt @{thm pred_sumE[OF TrueI]},
              hyp_subst_tac_thin true ctxt,
              rtac ctxt imageE,
              K (prefer_tac 2),
              eresolve_tac ctxt (flat valid_Udtor'),
              assume_tac ctxt,
              K (prefer_tac 3),
              assume_tac ctxt,
              eresolve_tac ctxt [UnI2, UnI1],
              EqSubst.eqsubst_tac ctxt [0] @{thms sum.set_map[of _ id, unfolded image_id, symmetric]},
              rtac ctxt @{thm setr.intros},
              rtac ctxt @{thm sym},
              assume_tac ctxt
            ])) goals end
          ) validUs (split_recs rec_sets) tds rawTs
        ) mrbnfs ds rs validUs picks suitables Utors raw_pre_setss;

        val suitable_prems = map2 (fn suitable => fn pick => HOLogic.mk_Trueprop (suitable $ pick))
        (map fst suitables) picks;

        val suitable_prems_all = @{map 3} (fn suitable => fn pick => fn pick' =>
          [HOLogic.mk_Trueprop (suitable $ pick), HOLogic.mk_Trueprop (suitable $ pick')])
        (map fst suitables) picks picks';

        val mutual = length mrbnfs > 1;

        val f_FVarsD_inner =
             @{map 4} (fn UFVarss =>  fn is_frees => fn is_free_induct  => fn nbfrees =>
          let
            val mk_inner_prem = fn a => fn is_free => fn valid => fn f => fn ufvars => fn t' => fn d =>
              let
                val zz = HOLogic.mk_imp (HOLogic.mk_eq (t', Term.list_comb (fst f, picks @ [d])),
                           (HOLogic.mk_mem (a, ufvars $ d)));
                val xx = (mk_all o dest_Free) d (HOLogic.mk_imp (valid $ d, zz));
                val yy = HOLogic.mk_imp (is_free $ a $ t', xx)
              in yy
              end

            val filter' = the o List.find (fn var => fastype_of var = HOLogic.dest_setT (body_type (fastype_of (hd UFVarss))))
            val a = filter' xs;
            val inner_prems = @{map 6} (fn ufvars => fn is_free => fn f => fn t' => fn d => fn valid =>
              let val inner_prem = mk_inner_prem a is_free valid f ufvars t' d;
               in inner_prem
               end) UFVarss is_frees fDefns ts ds validUs;
 
            val prems_conjed = fold_rev Logic.all (a :: ts)
                  (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj inner_prems));

            val subgoalN = nrecs + nbfrees;

          in Goal.prove_sorry lthy (names (picks @ ds)) suitable_prems prems_conjed (fn {context=ctxt, prems} => EVERY1 ([
            DETERM o (if mutual then rtac ctxt is_free_induct else rtac ctxt impI THEN' etac ctxt is_free_induct)
          ] @ flat (@{map 5} (
            fn ufvars => fn suitable_prem' => fn suitable_FVarsD'' => fn mrbnf' => fn valid_pick_set' =>
            let val n_free = length (filter (fn ty => ty = (HOLogic.dest_setT (body_type (fastype_of ufvars)))) frees);
                val vps = (map (fn thm => thm OF [suitable_prem']) (flat valid_pick_set'));
             in ((map (fn _ =>
              EVERY' [
                rtac ctxt allI,
                REPEAT_DETERM o rtac ctxt impI,
                TRY o EVERY' [
                  dtac ctxt @{thm DiffI},
                  assume_tac ctxt
                ],
                eresolve_tac ctxt (map (fn t =>
                  let val t' = Local_Defs.unfold0 lthy [@{thm Un_assoc}] (t OF [suitable_prem']);
                   in t' RS set_mp
                   end) suitable_FVarsD''),
                dresolve_tac ctxt f_ctor,
                hyp_subst_tac ctxt,
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf'),
                  REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}))
                ],
                SELECT_GOAL (Local_Defs.unfold_tac ctxt @{thms image_id Un_assoc[symmetric]}),
                REPEAT_DETERM o (eresolve_tac ctxt [UnI1, UnI2] ORELSE' rtac ctxt UnI1)
              ]) (1 upto n_free)) @ flat (map (fn goalN => [
                rtac ctxt allI,
                REPEAT_DETERM o rtac ctxt impI,
                forward_tac ctxt f_ctor,
                hyp_subst_tac ctxt,
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf'),
                  REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}))
                ],
                TRY o K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
                etac ctxt imageE,
                hyp_subst_tac ctxt,
                dresolve_tac ctxt (flat f_FVarsD_aux),
                etac ctxt allE,
                etac ctxt impE,
                K (prefer_tac 2),
                etac ctxt impE,
                REPEAT_DETERM o assume_tac ctxt,
                K (prefer_tac 2),
                rtac ctxt refl,
                K (prefer_tac 2),
                resolve_tac ctxt (map (fn t => Drule.rotate_prems 1 (t RS subsetD)) (flat suitable_FVarsD)),
                assume_tac ctxt,
                K (Local_Defs.unfold0_tac ctxt @{thms Un_assoc}),
                rtac ctxt UnI2,
                TRY o K (Local_Defs.unfold0_tac ctxt @{thms Un_assoc[symmetric]}),
                resolve_tac ctxt [BNF_Util.mk_UnIN (subgoalN) (goalN + nbfrees)],
                TRY o EVERY' [
                  rtac ctxt @{thm DiffI[rotated]},
                  assume_tac ctxt
                ],
                rtac ctxt @{thm UN_I},
                REPEAT_DETERM o assume_tac ctxt,
                resolve_tac ctxt prems,
                dresolve_tac ctxt vps,
                REPEAT_DETERM o assume_tac ctxt
              ]
          ) (1 upto nrecs))) end) UFVarss prems suitable_FVarsD mrbnfs valid_pick_set))) end                                                                                                                          
        ) (transpose UFVarsss) is_freess is_free_inducts nbfrees;

         val f_FVarsD = @{map 4} (fn FVarss => fn FVars_raw_defs => fn UFVarss => fn f_FVarsD_inner' =>
          let       
            val goals = @{map 5} (fn FVars => fn UFVars => fn fFun => fn d => fn validU =>
              let
              val lhs = FVars $ Term.list_comb (fst fFun, picks @ [d]);

              val rhs = UFVars $ d;

              val valid_prem = HOLogic.mk_Trueprop (validU $ d);
              val goal = Logic.mk_implies (valid_prem, HOLogic.mk_Trueprop (mk_leq lhs rhs));

              in
                goal
              end)               
              FVarss UFVarss fDefns ds validUs;

              val split_conj = split_conj (length UFVarss);
              val inners = split_conj (f_FVarsD_inner');

          in map2 (fn goal => fn inner => Goal.prove_sorry lthy (names (picks @ ds)) suitable_prems goal (fn {context=ctxt, prems} =>
            let val inner' = Drule.rotate_prems 1 ((inner OF prems) RS mp RS spec RS mp RS mp);
            in EVERY1 [
              rtac ctxt subsetI,
              etac ctxt inner',
              rtac ctxt refl,
              K (Local_Defs.unfold0_tac ctxt (@{thm mem_Collect_eq} :: FVars_raw_defs)),
              assume_tac ctxt
          ] end)) goals inners end
        ) (transpose (map #FVarss (#raw_fps fp_res))) (transpose FVars_raw_defss) (transpose UFVarsss) f_FVarsD_inner;

        val valid_tac = fn ctxt => fn valid_prem => fn suitable_prems => EVERY' [
             dresolve_tac ctxt (map (fn t => (Drule.rotate_prems 1 t) RS @{thm sum.pred_set[THEN fun_cong, THEN iffD1]}) (flat (flat valid_pick_set))),
             rtac ctxt valid_prem,
             resolve_tac ctxt suitable_prems,
             etac ctxt conjE,
             rotate_tac ~1,
             etac ctxt ballE,
             assume_tac ctxt,
             etac ctxt @{thm cnf.clause2raw_notE[THEN FalseE, rotated]},
             TRY o K (Local_Defs.unfold0_tac ctxt @{thms o_id}),
             REPEAT_DETERM o assume_tac ctxt
             ];

        val rel_F_suitable_mapD = @{map 11} (fn mrbnf => fn suitable => fn DTOR_mapD' => fn raw_pre_sets =>
                                 fn d => fn pick => fn pick' => fn valid_prem => fn Umap => fn suitable_prems =>
                                 fn raw_Umap_Utor' =>
         let
           val raw_UFVarsBDs = mk_FVarsBDs (transpose (map #FVarss (#raw_fps fp_res))) raw_pre_sets (pick $ d);
           val id_ons = map2 (fn f => fn fvar_union =>
             mk_id_on fvar_union f
           ) gs raw_UFVarsBDs;

           fun mk_mr_rel deads mrbnf =
             let
               val live_Ts = plives @ replicate_rec (map2 (fn uT => fn T => (mk_sumT (T, uT))) uTs rawTs);
             in
               MRBNF_Def.mk_mr_rel_of_mrbnf deads live_Ts live_Ts (pbounds @ vars) (vars @ pfrees @ bfrees) mrbnf  
           end;

           val comp_f_g = map2 (fn f => fn g => HOLogic.mk_comp (f, g));
           val f_comp_gs = comp_f_g fs gs;
           val bfree_f_comp_gs = comp_f_g bfree_fs bfree_gs;

           val rel_sums = @{map 8} (fn rec_bounds => fn alpha => fn t => fn t' => fn d => fn d' => fn raw_permute => fn Umap =>
             if null rec_bounds then
             let
               val (tName, tT) = dest_Free t;
               val (tName', tT') = dest_Free t';
               val L = Abs (tName, tT, Abs (tName', tT',
                 Term.list_comb (alpha, [Term.list_comb (raw_permute, fs @ [Bound 1]), Bound 0])));
              
               val (dName, dT) = dest_Free d;
               val (dName', dT') = dest_Free d';
               val R = Abs (dName, dT, Abs (dName', dT',
                 HOLogic.mk_eq
                   ( Term.list_comb (Umap, fs @ [Bound 1])
                   , Bound 0
                   )));
             in
               mk_rel_sum (L, R)
               end
             else let
               val fs' = map_index (fn (i, f) => if member (op=) rec_bounds i
                     then HOLogic.mk_comp (f, nth gs i)
                     else f
                   ) fs
  
               val (tName, tT) = dest_Free t;
               val (tName', tT') = dest_Free t';
               val L = Abs (tName, tT, Abs (tName', tT',
                 Term.list_comb (alpha, [Term.list_comb (raw_permute, fs' @ [Bound 1]), Bound 0])));
              
               val (dName, dT) = dest_Free d;
               val (dName', dT') = dest_Free d';
               val R = Abs (dName, dT, Abs (dName', dT',
                 HOLogic.mk_eq
                   ( Term.list_comb (Umap, fs' @ [Bound 1])
                   , Bound 0
                   )));
             in
               mk_rel_sum (L, R)
             end
           ) rec_boundss (replicate_rec alphas) (replicate_rec ts) (replicate_rec ts')
             (replicate_rec ds) (replicate_rec ds') (replicate_rec (map #permute (#raw_fps fp_res)))
             (replicate_rec Umaps);

           val lives = map HOLogic.eq_const plives @ rel_sums;
           val bounds' = map HOLogic.id_const pbounds @ f_comp_gs;
           val frees' = fs @ map HOLogic.id_const pfrees @ bfree_f_comp_gs;

           val mr_rel_term = Term.list_comb (
               mk_mr_rel (MRBNF_Def.deads_of_mrbnf mrbnf) mrbnf,
               MRBNF_Def.interlace lives bounds' frees' (MRBNF_Def.var_types_of_mrbnf mrbnf)
             ) $ (pick $ d) $ (pick' $ Term.list_comb (Umap, (fs @ [d])));

           val goal = HOLogic.mk_Trueprop (fold_rev (mk_ex o dest_Free) gs
                     (foldr1 HOLogic.mk_conj (alternate 2 1 g_prems' id_ons @ [mr_rel_term])));

           val nargs = MRBNF_Def.live_of_mrbnf mrbnf + MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf;

           val prems = valid_prem :: suitable_prems @ f_prems;

         in Goal.prove_sorry lthy (names ([d, pick, pick'] @ fs)) prems goal (fn {context=ctxt, prems as (valid_prem :: prem_rest)} =>
           let val (suitable_prems as [suitable_prem1, suitable_prem2], f_prems) = chop (length suitable_prems) prem_rest;
           val raw_Umap_Utor_inst =
             let val thm = Local_Defs.unfold0 lthy [@{thm rel_set_def}] (raw_Umap_Utor' OF (f_prems @ [valid_prem]));
             in thm RS conjunct2 RS bspec RS bexE
             end;
           in EVERY1 [
           rtac ctxt raw_Umap_Utor_inst,
           rtac ctxt allE,
           rtac ctxt (Local_Defs.unfold0 lthy [snd suitable] suitable_prem2),
           etac ctxt impE,
           K (prefer_tac 2),
           assume_tac ctxt,
           EVERY' [
             resolve_tac ctxt valid_Umaps,
             REPEAT_DETERM o resolve_tac ctxt (f_prems @ [valid_prem])
           ],
           rtac ctxt exE,
           rtac ctxt (DTOR_mapD' OF [valid_prem]),
           K (Local_Defs.unfold0_tac ctxt @{thms insert_subset}),
           rtac ctxt conjI,
           rtac ctxt ((Local_Defs.unfold0 lthy [snd suitable] suitable_prem1) RS spec RS mp OF [valid_prem]),
           
           rtac ctxt conjI,
           
           assume_tac ctxt,
           rtac ctxt @{thm empty_subsetI},
           REPEAT_DETERM o eresolve_tac ctxt [conjE, exE],
           REPEAT_DETERM o rtac ctxt exI,
           REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
           rotate_tac ~1,
           dtac ctxt (Drule.rotate_prems ~1 (MRBNF_Def.mr_rel_OO_of_mrbnf mrbnf RS fun_cong RS fun_cong RS iffD2) OF @{thms relcomppI}),
           assume_tac ctxt,
           REPEAT_DETERM o (resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems) ORELSE' assume_tac ctxt),
           K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id eq_OO sum.rel_compp[symmetric]}),
           etac ctxt (Drule.rotate_prems (~(nargs + 1)) (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf)),
           REPEAT_DETERM o EVERY' [
             REPEAT_DETERM o rtac ctxt ballI,
             resolve_tac ctxt @{thms refl imp_refl}
           ],
           K (Local_Defs.unfold_tac ctxt @{thms relcompp_apply}),
           REPEAT_DETERM o (EVERY' [
             REPEAT_DETERM o rtac ctxt ballI,
             rtac ctxt impI,
             etac ctxt @{thm sum.rel_cong[OF refl refl, THEN iffD1, rotated -1]},
             TRY o rtac ctxt iffI,
             etac ctxt exE,
             etac ctxt conjE,
             rotate_tac ~1,
             dresolve_tac ctxt (map (fn t => Drule.rotate_prems 1 t) (map (#alpha_trans o #inner) (#raw_fps fp_res))),
             eresolve_tac ctxt (map (fn t => Drule.rotate_prems ~1 (t RS iffD2)) (map (#alpha_bij_eq o #inner) (#raw_fps fp_res))),
             REPEAT_DETERM o (resolve_tac ctxt prems ORELSE' assume_tac ctxt),
             dresolve_tac ctxt (map (fn t => Drule.rotate_prems ~1 (t RS iffD1)) (map (#alpha_bij_eq_inv o #inner) (#raw_fps fp_res))),
             REPEAT_DETERM o (resolve_tac ctxt (prems @ [exI, conjI]) ORELSE' assume_tac ctxt),
             EqSubst.eqsubst_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
             REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms bij_imp_bij_inv supp_inv_bound}),
             REPEAT_DETERM o EVERY' [
               EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
               resolve_tac ctxt prems
             ],
             K (Local_Defs.unfold0_tac ctxt (map #permute_id (#raw_fps fp_res))),
             resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
             rtac ctxt refl
           ] ORELSE' EVERY' [
             REPEAT_DETERM o rtac ctxt ballI,
             rtac ctxt impI,
             etac ctxt @{thm sum.rel_mono_strong},
             REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
             rotate_tac ~1,
             dresolve_tac ctxt (map (fn t => Drule.rotate_prems 1 t) (map (#alpha_trans o #inner) (#raw_fps fp_res))),
             eresolve_tac ctxt (map (fn t => Drule.rotate_prems ~1 (t RS iffD2)) (map (#alpha_bij_eq o #inner) (#raw_fps fp_res))),
             REPEAT_DETERM o resolve_tac ctxt prems,
             EVERY' [
               EqSubst.eqsubst_asm_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
               REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}))
             ],
             TRY o K (Local_Defs.unfold0_tac ctxt @{thms o_id}),
             TRY o assume_tac ctxt,
             etac ctxt exE,
             etac ctxt conjE,
             hyp_subst_tac ctxt,
             rtac ctxt sym,
             rtac ctxt trans,
             resolve_tac ctxt Umap_comps,
             TRY o K (Local_Defs.unfold0_tac ctxt @{thms o_id}),
             valid_tac ctxt valid_prem suitable_prems,
             REPEAT_DETERM o (resolve_tac ctxt (prems @ @{thms refl supp_id_bound bij_id}) ORELSE' assume_tac ctxt)
           ]
           ),
           REPEAT_DETERM o (resolve_tac ctxt (f_prems @ @{thms bij_comp supp_comp_bound supp_id_bound infinite_UNIV}) ORELSE' assume_tac ctxt)
         ] end) end
       ) mrbnfs suitables DTOR_mapD raw_pre_setss ds picks picks' valid_prems Umaps suitable_prems_all raw_Umap_Utor;

        val f_swap_alpha =
         let          
           val alpha_subgoals = @{map 5} (fn alpha => fn d => fn raw_permute => fn fDefn => fn Umap =>
             alpha
               $ (Term.list_comb (raw_permute, fs @ [Term.list_comb (fDefn, picks @ [d])]))
               $ (Term.list_comb (fDefn, picks' @ [Term.list_comb (Umap, fs @ [d])]))
             ) alphas ds (map #permute (#raw_fps fp_res)) (map fst fDefns) Umaps;

           val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj alpha_subgoals);

           val prems = flat (transpose suitable_prems_all) @ valid_prems @ f_prems;
           val split_prems = fn ps =>
             let val (suitables, ps') = chop (length (flat suitable_prems_all)) ps;
                 val (valids, f_prems) = chop (length valid_prems) ps'
             in (transpose (chop_groups (length suitable_prems_all) suitables), valids, f_prems)
             end;

           val (conj_spec, conj_mp, _) = mk_conj_thms (length ds) lthy;

           val REPEAT_NRECS = REPEAT_DETERM_N nrecs;

           val coinduct_inst_args = @{map 7} (fn tL => fn tR => fn d => fn raw_permute => fn fDefn =>
                                              fn Umap => fn validU =>
             let val term_tL =
               (HOLogic.mk_eq (tL,
                 (Term.list_comb (raw_permute, fs @ [Term.list_comb (fDefn, picks @ [d])]))));

                 val term_tR =
                 (HOLogic.mk_eq (tR,
                   (Term.list_comb (fDefn, picks' @ [Term.list_comb (Umap, fs @ [d])]))));
              in
                 Term.absfree (dest_Free tL)
                   (Term.absfree (dest_Free tR)
                     (fold_rev (mk_ex o dest_Free) (fs @ [d])
                       (foldr1 HOLogic.mk_conj (validU $ d :: f_prems' @ [term_tL, term_tR]))))
              end
             ) ts ts' ds (map #permute (#raw_fps fp_res)) (map fst fDefns) Umaps validUs;

           val coinduct_inst = fn ctxt => (infer_instantiate' ctxt (map (fn t => SOME (Thm.cterm_of lthy t)) coinduct_inst_args) coinductThm);

         in Goal.prove_sorry lthy (names (picks @ picks' @ ds @ fs)) prems goal (fn {context=ctxt, prems} =>
           let
             val (suitable_prems, valid_prems, f_prems) = split_prems prems;
             val [p, p'] = transpose suitable_prems;
             val FVars_raw_permutes = map #FVars_permutes (#raw_fps fp_res);

             val coinduct_inst' =
               if mutual
               then coinduct_inst ctxt RS conj_spec RS conj_spec RS conj_mp
               else coinduct_inst ctxt;
             val coinduct_inst'' =
               if mutual
                 then rtac ctxt coinduct_inst'
                 else EVERY' [
                   rtac ctxt coinduct_inst',
                   defer_tac
                 ];
            in
             EVERY1 [
               coinduct_inst'',
               EVERY' (@{map 5} (fn mrbnf => fn exhaust => fn inject => fn rel_F_suitable_mapD' =>
                                 fn suitable_prems' =>
                 let val nargs = MRBNF_Def.live_of_mrbnf mrbnf + MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf;
                 in EVERY' [
                 Subgoal.FOCUS_PARAMS (fn {params as [(_,x1), (_,x2)], context = ctxt, ...} => EVERY1 [
                   REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
                   rtac ctxt (infer_instantiate' ctxt [SOME x1] exhaust),
                   dtac ctxt @{thm trans[OF sym]},
                   assume_tac ctxt,
                   rtac ctxt (infer_instantiate' ctxt [SOME x2] exhaust),
                   dtac ctxt @{thm trans[OF sym]},
                   assume_tac ctxt,
                   hyp_subst_tac_thin true ctxt,
                   SELECT_GOAL (Local_Defs.unfold0_tac ctxt f_simps),
                   EqSubst.eqsubst_asm_tac ctxt [0] (map #permute_ctor (#raw_fps fp_res)),
                   REPEAT_DETERM o assume_tac ctxt,
                   REPEAT_DETERM o dtac ctxt (iffD1 OF [inject]),
                   EqSubst.eqsubst_asm_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                   REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}) ORELSE' assume_tac ctxt),
                   SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
                   hyp_subst_tac ctxt,
                   forward_tac ctxt [rel_F_suitable_mapD' OF (@{thm _} :: suitable_prems')],
                   REPEAT_DETERM o assume_tac ctxt,
                   REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
                   REPEAT_DETERM o rtac ctxt exI,
                   REPEAT_DETERM o EVERY' [
                     rtac ctxt conjI,
                     rtac ctxt refl
                   ],
                   REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
                   rtac ctxt (Drule.rotate_prems ~1 ((nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 0) RS iffD2)),
                   SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms id_o o_id Grp_UNIV_id eq_OO}),
                   rtac ctxt (Drule.rotate_prems ~1 ((nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2) RS iffD2)),
                   SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms inv_id id_o o_id Grp_UNIV_id eq_OO conversep_eq}),
                   etac ctxt (Drule.rotate_prems (~(nargs + 1)) (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf)),
                   REPEAT_DETERM o EVERY' [
                     REPEAT_DETERM o rtac ctxt ballI,
                     resolve_tac ctxt @{thms refl imp_refl}
                   ],
                   REPEAT_DETERM o EVERY' [
                     rtac ctxt ballI,
                     rtac ctxt @{thm comp_inv_aux[THEN fun_cong]},
                     assume_tac ctxt
                   ],
                   REPEAT_NRECS o defer_tac,
                   REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id bij_comp supp_comp_bound_var bij_imp_bij_inv supp_inv_bound}),
                   REPEAT_DETERM o EVERY' [
                     rtac ctxt @{thm id_on_f_inv_f},
                     assume_tac ctxt,
                     REPEAT_DETERM o EVERY' [
                       EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                       REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound bij_id}))
                     ],
                     etac ctxt @{thm id_on_antimono},
                     SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms image_comp[unfolded comp_def] comp_apply image_Un}),
                     REPEAT_DETERM o EVERY' [
                       EqSubst.eqsubst_tac ctxt [0] (flat FVars_raw_permutes),
                       REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound bij_id}))
                     ],
                     SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv]] image_comp inv_o_simp1 image_id image_UN[symmetric] Un_Diff[symmetric]}),
                     rtac ctxt @{thm Diff_mono[OF _ subset_refl]},
                     rtac ctxt subsetI,
                     TRY o REPEAT_DETERM o etac ctxt UnE,
                     REPEAT_DETERM o EVERY' [
                       REPEAT_DETERM o ((EVERY' [TRY o rtac ctxt UnI2, etac ctxt @{thm UN_mono[THEN subsetD, OF subset_refl, rotated -1]}]) ORELSE' rtac ctxt UnI1 ORELSE' assume_tac ctxt),
                       Subgoal.FOCUS_PARAMS (fn {params, context = ctxt, ...} => let val (_,(_,x)) = split_last params in
                         case try (infer_instantiate' ctxt [SOME x]) @{thm sumE} of
                           SOME thm => rtac ctxt thm 1
                           | NONE => no_tac
                       end) ctxt,
                       hyp_subst_tac_thin true ctxt,
                       K (Local_Defs.unfold0_tac ctxt @{thms sum.simps id_apply}),
                       rtac ctxt subset_refl,
                       hyp_subst_tac_thin true ctxt,
                       K (Local_Defs.unfold0_tac ctxt @{thms sum.simps}),
                       resolve_tac ctxt (flat (map (map (fn t => t OF p)) f_FVarsD)),
                       dresolve_tac ctxt (map (fn t => Drule.rotate_prems 1 t) (flat (flat valid_pick_set))),
                       assume_tac ctxt,
                       resolve_tac ctxt p,
                       K (Local_Defs.unfold0_tac ctxt @{thms pred_sum_inject}),
                       assume_tac ctxt
                     ]
                   ],
                   REPEAT_DETERM o (resolve_tac ctxt @{thms supp_comp_bound_var supp_inv_bound bij_comp bij_imp_bij_inv infinite_UNIV} ORELSE' assume_tac ctxt),
                   REPEAT_DETERM o EVERY' [
                     REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
                     SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms relcompp_conversep_Grp}),
                     SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Grp_OO}),
                     rtac ctxt disjCI,
                     etac ctxt @{thm rel_sum.cases},
                     hyp_subst_tac ctxt,
                     K (Local_Defs.unfold0_tac ctxt @{thms sum.case comp_apply id_apply}),
                     TRY o EVERY' [
                       EVERY' [
                         EqSubst.eqsubst_asm_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                         REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound infinite_UNIV})
                       ],
                       SELECT_GOAL (Local_Defs.unfold_tac ctxt @{thms comp_assoc}),
                       REPEAT_DETERM o EVERY' [
                         EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp1},
                         assume_tac ctxt
                       ],
                       K (Local_Defs.unfold_tac ctxt @{thms id_o o_id})
                     ],
                     etac ctxt @{thm cnf.clause2raw_notE[THEN FalseE, rotated]},
                     assume_tac ctxt,
                     hyp_subst_tac ctxt,
                     K (Local_Defs.unfold0_tac ctxt @{thms sum.case comp_apply id_apply}),
                     REPEAT_DETERM o rtac ctxt exI,
                     rtac ctxt conjI,
                     dresolve_tac ctxt (map (fn t => Drule.rotate_prems 1 t) (flat (flat valid_pick_set))),
                     assume_tac ctxt,
                     resolve_tac ctxt p,
                     K (Local_Defs.unfold0_tac ctxt @{thms pred_sum_inject}),
                     rotate_tac ~1,
                     assume_tac ctxt,
                     REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
                     resolve_tac ctxt (map (fn t => t RS arg_cong) f_simps),
                     TRY o EVERY' [
                       EVERY' [
                         EqSubst.eqsubst_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                         REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound infinite_UNIV})
                       ],
                       SELECT_GOAL (Local_Defs.unfold_tac ctxt @{thms comp_assoc}),
                       REPEAT_DETERM o EVERY' [
                         EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
                         assume_tac ctxt
                       ],
                       K (Local_Defs.unfold_tac ctxt @{thms id_o o_id})
                     ],
                     resolve_tac ctxt (map (fn t => t RS arg_cong) f_simps),
                     REPEAT_DETERM o (resolve_tac ctxt @{thms supp_comp_bound bij_comp infinite_UNIV} ORELSE' assume_tac ctxt)
                   ]
                 ]) ctxt                 
               ] end) mrbnfs (map (#exhaust o #inner) (#raw_fps fp_res)) (map #inject (#raw_fps fp_res))
                  rel_F_suitable_mapD suitable_prems),
               REPEAT_DETERM_N (length uTs) o EVERY' [
                   REPEAT_DETERM o rtac ctxt exI,
                   REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
                   REPEAT_DETERM o rtac ctxt refl,
                   REPEAT_DETERM o resolve_tac ctxt prems
                 ]
             ] end)
         end
       ;

      val f_alpha =
         let          
           val alpha_subgoals = @{map 3} (fn alpha => fn d => fn fDefn =>
             alpha
               $ (Term.list_comb (fDefn, picks @ [d]))
               $ (Term.list_comb (fDefn, picks' @ [d]))
             ) alphas ds (map fst fDefns);

           val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj alpha_subgoals);

           val prems = flat (transpose suitable_prems_all) @ valid_prems;

           val split_prems = fn ps =>
             let val (suitables, ps') = chop (length (flat suitable_prems_all)) ps;
                 val (valids, f_prems) = chop (length valid_prems) ps'
             in (transpose (chop_groups (length suitable_prems_all) suitables), valids, f_prems)
             end;

         in Goal.prove_sorry lthy (names (picks @ picks' @ ds)) prems goal (fn {context=ctxt, prems} =>
           let
             val (_, valid_prems, _) = split_prems prems;
             val f_swap_alpha_inst = f_swap_alpha OF (prems @ flat (replicate (length mrbnfs) @{thms bij_id supp_id_bound}));
             val Umap_id_inst = map2 (fn t => fn valid => t OF [valid]) Umap_ids valid_prems;
             val f_swap_alpha' = Local_Defs.unfold0 lthy ((map #permute_id (#raw_fps fp_res)) @ Umap_id_inst) f_swap_alpha_inst
            in rtac ctxt f_swap_alpha' 1 end)
         end
       ;

       val exists_suitable =
         let
           val goals = map2 (fn s => fn pick => HOLogic.mk_Trueprop (mk_ex (dest_Free pick) (s $ pick))) (map fst suitables) picks;
         in map (fn goal => Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, ...} =>
            EVERY1 [
              K (Local_Defs.unfold0_tac ctxt (map snd suitables)),
              rtac ctxt @{thm choice},
              rtac ctxt allI,
              EqSubst.eqsubst_tac ctxt [0] @{thms ex_simps},
              rtac ctxt impI,
              eresolve_tac ctxt (map (fn thm => thm RS @{thm ex_in_conv[THEN iffD2]}) Utor_ne)
            ])) goals
         end
       ;

       val suitable_pick0 = map2 (fn exists_suitable' => fn pick0 =>
         Local_Defs.fold lthy [pick0] (@{thm someI_ex} OF [exists_suitable']))
         exists_suitable (map snd pick0s);

      val f0_Utor_aux = @{map 6} (fn alpha => fn d => fn rawX => fn fFun => fn raw_ctor => fn mrbnf =>
          let
            val utor_prems = @{map 3} (fn rawX => fn d => fn Utor =>
              HOLogic.mk_Trueprop (HOLogic.mk_mem (rawX, Utor $ d))) rawXs ds (map fst Utors);

            val prems = utor_prems @ valid_prems;

            val split_prems = fn ps => chop (length utor_prems) ps;

            val alphaL_lambdas = @{map 4} (fn d => fn d' => fn rawX => fn pick0 =>
              (Term.absfree (dest_Free d') (BNF_FP_Util.mk_If (
                HOLogic.eq_const (fastype_of d) $ (Bound 0) $ d) rawX (pick0 $ Bound 0)))
              ) ds ds' rawXs (map fst pick0s);

            val alphaL = Term.list_comb (fst fFun, alphaL_lambdas @ [d]);

            val case_sum_args = map2 (fn rawT => fn f =>
              BNF_FP_Util.mk_case_sum ((HOLogic.id_const rawT), f))
              (replicate_rec rawTs) (replicate_rec (map fst f0Defns));

            val case_fun = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ case_sum_args)
              (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
              mrbnf;

            val alphaR = raw_ctor $ (case_fun $ rawX);
            
            val goal = HOLogic.mk_Trueprop (alpha $ alphaL $ alphaR);

            val alpha_intros = map (#alpha_intro o #inner) (#raw_fps fp_res);

            val suitable_pick0_unfolded = map (fn t => (Local_Defs.unfold0 lthy (map snd suitables) t) RS spec RS mp) suitable_pick0;

            val split_conj = split_conj (length alphas);
            val f_alpha_inst = split_conj (f_alpha OF (replicate (length mrbnfs) @{thm _} @ suitable_pick0));

          in Goal.prove_sorry lthy (names (ds @ rawXs)) prems goal (fn {context=ctxt, prems} =>
            let val (utor_prems, valid_prems) = split_prems prems;
             in EVERY1 [
            EqSubst.eqsubst_tac ctxt [0] f_simps,
            EqSubst.eqsubst_tac ctxt [0] @{thms if_P[OF refl]},
            EVERY' [
              resolve_tac ctxt alpha_intros,
              REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound id_on_id}
            ],
            K (Local_Defs.unfold0_tac ctxt ((MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym) :: MRBNF_Def.rel_map_of_mrbnf mrbnf)),
            rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
            REPEAT_DETERM o rtac ctxt refl,
            REPEAT_DETERM o EVERY' [
              rtac ctxt @{thm sumE},
              forward_tac ctxt @{thms arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1]},
              assume_tac ctxt,
              hyp_subst_tac ctxt,
              K (Local_Defs.unfold0_tac ctxt @{thms sum.simps}),
              TRY o K (Local_Defs.unfold0_tac ctxt (@{thm id_apply} :: map #permute_id (#raw_fps fp_res))),
              resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
              hyp_subst_tac ctxt,
              K (Local_Defs.unfold0_tac ctxt @{thms sum.simps}),
              TRY o K (Local_Defs.unfold0_tac ctxt (map snd f0Defns)),
              resolve_tac ctxt f_alpha_inst,
              REPEAT_DETERM_N (length suitables) o EVERY' [
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt (map snd suitables)),
                rtac ctxt allI,
                rtac ctxt impI,
                rtac ctxt @{thm if_split[THEN iffD2]},
                rtac ctxt conjI,
                rtac ctxt impI,
                hyp_subst_tac ctxt,
                resolve_tac ctxt prems,
                rtac ctxt impI,
                resolve_tac ctxt suitable_pick0_unfolded,  
                assume_tac ctxt
              ],
              TRY o resolve_tac ctxt prems,
              resolve_tac ctxt (map (fn t => (Local_Defs.unfold0 lthy (map snd Utors) t) RS imageE) utor_prems),
              rotate_tac ~1,
              eresolve_tac ctxt (map (fn t => Drule.rotate_prems 1 t) (flat valid_Udtor')),
              K (prefer_tac 2),
              rtac ctxt @{thm setr.intros},
              rtac ctxt refl,
              hyp_subst_tac_thin true ctxt,
              EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id}))
              ],
              etac ctxt imageE,
              dresolve_tac ctxt @{thms setr.intros[OF sym]},
              K (Local_Defs.unfold0_tac ctxt @{thms sum.set_map image_id setr.simps}),
              etac ctxt exE,
              etac ctxt conjE,
              hyp_subst_tac_thin true ctxt,
              eresolve_tac ctxt [UnI1, UnI2],
              REPEAT_DETERM o resolve_tac ctxt prems
            ]
          ] end) end
        ) alphas ds rawXs fDefns (map #ctor (#raw_fps fp_res)) mrbnfs;

      val f0_Utor = @{map 6} (fn alpha => fn d => fn rawX => fn f0Fun => fn raw_ctor => fn mrbnf =>
          let
            val utor_prems = @{map 3} (fn rawX => fn d => fn Utor =>
              HOLogic.mk_Trueprop (HOLogic.mk_mem (rawX, Utor $ d))) rawXs ds (map fst Utors);

            val prems = utor_prems @ valid_prems;

            val split_prems = fn ps => chop (length utor_prems) ps;

            val alphaL = fst f0Fun $ d;

            val case_sum_args = map2 (fn rawT => fn f =>
              BNF_FP_Util.mk_case_sum ((HOLogic.id_const rawT), f))
              (replicate_rec rawTs) (replicate_rec (map fst f0Defns));

            val case_fun = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ case_sum_args)
              (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
              mrbnf;

            val alphaR = raw_ctor $ (case_fun $ rawX);
            
            val goal = HOLogic.mk_Trueprop (alpha $ alphaL $ alphaR);

            val suitable_pick0_unfolded = map (fn t => (Local_Defs.unfold0 lthy (map snd suitables) t) RS spec RS mp) suitable_pick0;

            val split_conj = split_conj (length alphas);

          in Goal.prove_sorry lthy (names (ds @ rawXs)) prems goal (fn {context=ctxt, prems} =>
            let val (utor_prems, valid_prems) = split_prems prems;
                val f_alpha_inst' = Local_Defs.fold lthy (map snd f0Defns) (f_alpha OF (suitable_pick0 @ replicate (length mrbnfs) @{thm _} @ valid_prems));
                val f_alpha_inst = split_conj f_alpha_inst';
             in EVERY1 [
               resolve_tac ctxt (map (fn t => Drule.rotate_prems 1 t) (map (#alpha_trans o #inner) (#raw_fps fp_res))),
               resolve_tac ctxt (map (fn t => t OF prems) f0_Utor_aux),
               resolve_tac ctxt f_alpha_inst,
               REPEAT_DETERM o EVERY' [
                 SELECT_GOAL (Local_Defs.unfold0_tac ctxt (map snd suitables)),
                 rtac ctxt allI,
                 rtac ctxt impI,
                 rtac ctxt @{thm if_split[THEN iffD2]},
                 rtac ctxt conjI,
                 rtac ctxt impI,
                 hyp_subst_tac ctxt,
                 resolve_tac ctxt prems,
                 rtac ctxt impI,
                 eresolve_tac ctxt suitable_pick0_unfolded
               ]
          ] end) end
        ) alphas ds rawXs f0Defns (map #ctor (#raw_fps fp_res)) mrbnfs;

        val alpha_syms = (map (#alpha_sym o #inner) (#raw_fps fp_res));

        val f0_mapD =
          let val split_conj = split_conj (length alphas);
              val splits = split_conj (f_swap_alpha OF (suitable_pick0 @ suitable_pick0));
           in @{map 3} (fn t => fn alpha_sym => fn f0Defn => Local_Defs.fold lthy [f0Defn] (t RS alpha_sym)) splits alpha_syms (map snd f0Defns)
           end;

        val f0_FVarsD = map (fn t => Local_Defs.fold lthy (map snd f0Defns) (t OF suitable_pick0)) (flat f_FVarsD);

        val COREC_DDTOR = @{map 5} (fn COREC => fn d => fn X => fn ctor => fn mrbnf =>
          let
            val udtor_prems = @{map 3} (fn X => fn d => fn Udtor =>
              HOLogic.mk_Trueprop (HOLogic.mk_mem (X, Udtor $ d))) Xs ds Udtors;

            val prems = udtor_prems @ valid_prems;

            val eqL = fst COREC $ d;

            val case_sum_args = map2 (fn T => fn f =>
              BNF_FP_Util.mk_case_sum ((HOLogic.id_const T), f))
              (replicate_rec qTs) (replicate_rec (map fst corecDefns));

            val case_fun = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
              (map HOLogic.id_const plives @ case_sum_args)
              (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
              mrbnf;

            val eqR = ctor $ (case_fun $ X);
            
            val goal = mk_Trueprop_eq (eqL, eqR);

            val alpha_intros = map (#alpha_intro o #inner) (#raw_fps fp_res);

          in Goal.prove_sorry lthy (names (ds @ Xs)) prems goal (fn {context=ctxt, prems} =>
            EVERY1 [
               K (Local_Defs.unfold_tac ctxt (map snd corecDefns @ map (#ctor_def o #inner) (#quotient_fps fp_res))),
               K (Local_Defs.unfold0_tac ctxt @{thms o_def[symmetric]}),
               EVERY' [
                 EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                 REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id})
               ],
               K (Local_Defs.unfold0_tac ctxt total_abs_eq_iffs),
               K (Local_Defs.unfold0_tac ctxt @{thms o_case_sum}),
               K (Local_Defs.unfold0_tac ctxt @{thms id_comp comp_id}),
               resolve_tac ctxt (map (#alpha_trans o #inner) (#raw_fps fp_res)),
               rtac ctxt @{thm arg_cong[THEN iffD1]},
               K (prefer_tac 2),
               resolve_tac ctxt f0_Utor,
               K (Local_Defs.unfold0_tac ctxt (map snd Utors)),
               REPEAT_DETERM o EVERY' [
                 rtac ctxt imageI,
                 REPEAT_DETERM o resolve_tac ctxt prems
               ],
               EVERY' [
                 EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                 REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id})
               ],
               K (Local_Defs.unfold0_tac ctxt @{thms case_sum_o_map_sum}),
               K (Local_Defs.unfold0_tac ctxt @{thms id_comp comp_id}),
               rtac ctxt refl,
               EVERY' [
                 resolve_tac ctxt alpha_intros,
                 REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id})
               ],
               REPEAT_DETERM o rtac ctxt @{thm id_on_id},
               K (Local_Defs.unfold0_tac ctxt ((MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym) :: MRBNF_Def.rel_map_of_mrbnf mrbnf)),
               rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
               TRY o rtac ctxt refl,
               REPEAT_DETERM o EVERY' [
                 rtac ctxt @{thm sumE},
                 forward_tac ctxt @{thms arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1]},
                 assume_tac ctxt,
                 hyp_subst_tac ctxt,
                 
                 K (Local_Defs.unfold0_tac ctxt @{thms sum.simps}),
                 TRY o K (Local_Defs.unfold0_tac ctxt (map #permute_id (#raw_fps fp_res))),
                 resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                 forward_tac ctxt @{thms arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1]},
                 assume_tac ctxt,
                 hyp_subst_tac ctxt,
                 K (Local_Defs.unfold0_tac ctxt @{thms sum.simps}),
                 SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_apply}),
                 resolve_tac ctxt (map (#rep_abs_sym o #inner) (#quotient_fps fp_res))
               ]
          ]) end
        ) corecDefns ds Xs (map #ctor (#quotient_fps fp_res)) mrbnfs;

        val COREC_mmapD = @{map 4} (fn COREC => fn d => fn Umap => fn permute =>
          let
            val prems = valid_prems @ f_prems;
            val split_prems = fn ps => chop (length valid_prems) ps;

            val eqL = fst COREC $ (Term.list_comb (Umap, (fs @ [d])));

            val eqR = Term.list_comb (permute, (fs @ [fst COREC $ d]));
            
            val goal = mk_Trueprop_eq (eqL, eqR);

          in Goal.prove_sorry lthy (names (ds @ fs)) prems goal (fn {context=ctxt, prems} =>
            let val (valid_prems, f_prems) = split_prems prems;
             in
            EVERY1 [
              K (Local_Defs.unfold_tac ctxt (map snd corecDefns @ map (#permute_def o #inner) (#quotient_fps fp_res))),
              K (Local_Defs.unfold0_tac ctxt total_abs_eq_iffs),
              resolve_tac ctxt (map (#alpha_trans o #inner) (#raw_fps fp_res)),
              resolve_tac ctxt (map (fn t => t OF prems) f0_mapD),
              K (Local_Defs.unfold0_tac ctxt (map ((fn t => t OF f_prems) o #alpha_bij_eq o #inner) (#raw_fps fp_res))),
              resolve_tac ctxt alpha_syms,
              resolve_tac ctxt (map (#rep_abs o #inner) (#quotient_fps fp_res))
          ] end) end
        ) corecDefns ds Umaps (map #permute (#quotient_fps fp_res));

         val COREC_FFVarsD = @{map 7} (fn COREC => fn d => fn FVarss => fn UFVarss => fn valid_prem => fn rep_abs => fn alpha_FVars =>
          let
            val goals = map2 (fn FVars => fn UFVars =>
              let
                val lhs = FVars $ (fst COREC $ d);
                val rhs = UFVars $ d;
              in
                Logic.mk_implies (valid_prem, HOLogic.mk_Trueprop (mk_leq lhs rhs))
              end) FVarss UFVarss;

            val alpha_FVars' = map (fn t => t OF [rep_abs]) alpha_FVars;

          in map (fn goal => Goal.prove_sorry lthy (names ds) [] goal (fn {context=ctxt, ...} =>
            EVERY1 [
              K (Local_Defs.unfold0_tac ctxt
                (snd COREC :: (flat (map (#FVars_defs o #inner) (#quotient_fps fp_res)) @ alpha_FVars'))),
              eresolve_tac ctxt f0_FVarsD
          ])) goals end
        ) corecDefns ds (map #FVarss (#quotient_fps fp_res)) UFVarsss valid_prems
          (map (#rep_abs o #inner) (#quotient_fps fp_res)) (map (#alpha_FVarss o #inner) (#raw_fps fp_res));

        val notes = [
          ("COREC_dtor", COREC_DDTOR),
          ("COREC_swap", COREC_mmapD),
          ("COREC_FVars", flat COREC_FFVarsD)
        ] |> (map (fn (thmN, thms) =>
          (((Binding.name thmN), []), [(thms, [])])
        ))
        val (_, lthy) = Local_Theory.notes notes lthy

      in (name, Local_Theory.exit_global lthy) end
    ) lthy;
    
  in (corecursor_result, lthy) end

end