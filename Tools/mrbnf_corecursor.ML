signature MRBNF_CORECURSOR =
sig
  type corecursor_result = {
    COREC: string,
    QCOREC: string,
    QCOREC_fixed: string
  };

  val create_binding_corecursor: (binding -> binding) -> MRBNF_FP_Def_Sugar.fp_result
    -> local_theory -> (* corecursor_result * *) local_theory;
  (*val get_CORECs: bool -> string -> local_theory -> term list;*)

end

structure MRBNF_Corecursor : MRBNF_CORECURSOR =
struct

open MRBNF_Util

type corecursor_result = {
  COREC: string,
  QCOREC: string,
  QCOREC_fixed: string
};

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

    val ((((Umaps, UFVarsss), Udtors), validUs), names_lthy) = names_lthy
      |> mk_Frees "Umap" (map (fn uT => fTs ---> uT --> uT) uTs)
      ||>> mk_Freess "UFVars" (map (fn uT => map (fn a => uT --> HOLogic.mk_setT a) vars) uTs)
      ||>> mk_Frees "Udtor" pre_Ts
      ||>> mk_Frees "validU" (map (fn uT => uT --> @{typ bool}) uTs);

    val ((((((((ds, fs), gs), Xs), Xs'), xs), picks), rawXs) , names_lthy) = names_lthy
      |> mk_Frees "d" uTs
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "g" fTs
      ||>> mk_Frees "X" (map (HOLogic.dest_setT o body_type) pre_Ts)
      ||>> mk_Frees "X'" (map (HOLogic.dest_setT o body_type) pre_Ts)
      ||>> mk_Frees "a" vars
      ||>> mk_Frees "pick" raw_pre_Ts
      ||>> mk_Frees "rawX" (map body_type raw_pre_Ts);
    val bfree_fs = map (nth fs) (#bfree_vars fp_res);

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

        val _ = @{print} (map (Thm.cterm_of lthy) (FFVarsBDs X));
        val _ = @{print} (map (Thm.cterm_of lthy) (raw_UFVarsBDs rawX));

        val id_ons = map2 (fn f => fn fvar_union =>
          mk_id_on fvar_union f
        ) fs (FFVarsBDs X);

        val binding_rel = map flat (#binding_relation fp_res);

        val rec_boundss = map (fn i =>
          @{map_filter 2} (fn j => fn rel =>
            if member (op=) rel i then SOME j else NONE
          ) (0 upto length binding_rel - 1) binding_rel
        ) (0 upto nrecs - 1);

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
              fun pred_True T = Term.abs ("_", T) @{term True};
              fun mk_pred_sum P Q =
                let
                  val PT = fastype_of P;
                  val QT = fastype_of Q;
                  val fT = mk_sumT (domain_type PT, domain_type QT);
                in Const (@{const_name pred_sum}, PT --> QT --> fT --> @{typ bool}) $ P $ Q end;
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
            (replicate_rec (map (#rep o #inner) (#quotient_fps fp_res))) (replicate_rec uTs);
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
        val _ = @{print} (map (Thm.cterm_of lthy) corecs);

        val (fDefns, lthy) = mk_defs_t "f" 1
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

        (* TODO: is this the way to do this definition? *)
        val (pick0s, lthy) = mk_defs_t "pick0_" 1
          (map2 (fn pick => fn suitable => HOLogic.choice_const (fastype_of pick) $
            (Term.absfree (dest_Free pick) (suitable $ pick)))
            picks (map fst suitables)) lthy;

        val (f0Defns, lthy) = mk_defs_t "f0_" 1
          (map (fn fDefn =>
            let
              val body = Term.list_comb (fDefn, (map fst pick0s));
            in
              body
            end) (map fst fDefns)) lthy;

        val (corecDefns, lthy) = mk_defs_t "COREC" 1
          (@{map 3} (fn d => fn abs => fn f0 =>
            (Term.absfree (dest_Free d) (abs $ (f0 $ d))))
            ds (map (#abs o #inner) (#quotient_fps fp_res)) (map fst f0Defns)) lthy;

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

        val _ = @{print} Utors;
        val _ = @{print} suitables;
        val _ = @{print} fDefns;
        val _ = @{print} pick0s;
        val _ = @{print} f0Defns;
        val _ = @{print} corecDefns;

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

        val _ = @{print} valid_Udtor'

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

        val FVarsBD_FFVarsBDs = @{map 4} (fn mrbnf => fn rawX => fn raw_pre_sets => fn pre_sets =>
          let
            val mk_FFVarsBDs = mk_FVarsBDs (transpose (map #FVarss (#quotient_fps fp_res))) pre_sets;
            val raw_UFVarsBDs = mk_FVarsBDs (transpose (map #FVarss (#raw_fps fp_res))) raw_pre_sets rawX;
            val map_sum_args = map2 (fn rep => fn uT =>
              mk_map_sum rep (HOLogic.id_const uT))
              (replicate_rec (map (#abs o #inner) (#quotient_fps fp_res))) (replicate_rec uTs);
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
                  (* K (Local_Defs.unfold0_tac ctxt <raw_UFVars_def2>) *)
              ])
              end
            ) raw_UFVarsBDs rhss
          end
        ) mrbnfs rawXs raw_pre_setss pre_setss;

        val _ = @{print} FVarsBD_FFVarsBDs;

      in (name, Local_Theory.exit_global lthy) end
    ) lthy;
    
  in lthy end

end