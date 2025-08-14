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

    (* val _ = @{print} vars; *)

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

    val ((((Umaps, UFVarsss), Udtors), validUs), names_lthy) = names_lthy
      |> mk_Frees "Umap" (map (fn uT => fTs ---> uT --> uT) uTs)
      ||>> mk_Freess "UFVars" (map (fn uT => map (fn a => uT --> HOLogic.mk_setT a) vars) uTs)
      ||>> mk_Frees "Udtor" pre_Ts
      ||>> mk_Frees "validU" (map (fn uT => uT --> @{typ bool}) uTs);

    val (((((ds, fs), gs), Xs), Xs'), names_lthy) = names_lthy
      |> mk_Frees "d" uTs
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "g" fTs
      ||>> mk_Frees "X" (map (HOLogic.dest_setT o body_type) pre_Ts)
      ||>> mk_Frees "X'" (map (HOLogic.dest_setT o body_type) pre_Ts);
    val bfree_fs = map (nth fs) (#bfree_vars fp_res);

    val lthy = no_defs_lthy;

    (* val _ = @{print} (#rec_vars fp_res); *)
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
    
    val mk_prems = maps (fn f => [mk_bij f, mk_supp_bound f]);
    val f_prems' = mk_prems fs;
    val f_prems = map HOLogic.mk_Trueprop f_prems';
    val g_prems' = mk_prems gs;
    val g_prems = map HOLogic.mk_Trueprop g_prems';
    val nvars = length vars;
    val nrecs = foldr1 (op+) (#rec_vars fp_res);

    val mk_map_sum = mk_bin_map @{const_name map_sum} BNF_Util.mk_sumT

    val goals = @{map 12} (fn i => fn name => fn mrbnf => fn d => fn X => fn X' => fn Umap => fn UFVarss => fn Udtor
      => fn validU => fn (rec_sets, bsets, fsets) => fn quot =>
      let
        val Udtor_ne = Logic.all d (Logic.mk_implies (
          HOLogic.mk_Trueprop (validU $ d),
          HOLogic.mk_Trueprop (
            HOLogic.mk_not (HOLogic.mk_eq (Udtor $ d, mk_bot (fastype_of X)))
          )
        ));


        val bfree_sets = flat (map (fn i => if member (op=) (#bfree_vars fp_res) i then
          [nth (drop nvars fsets) i] else []
        ) (0 upto nvars - 1));
        val bfree_setss = map (fn i => if member (op=) (#bfree_vars fp_res) i then
          [nth (drop nvars fsets) i $ X] else []
        ) (0 upto nvars - 1);

        val fsets = take nvars fsets;

(*
        val _ = @{print} (map (Thm.cterm_of lthy) lsets);
        val _ = @{print} (map (Thm.cterm_of lthy) bsets);
        val _ = @{print} (map (Thm.cterm_of lthy) fsets);
        val _ = @{print} ((map (Thm.cterm_of lthy)) bfree_sets);
*)
        val purefsets = filter (fn x => not (member (op=) bfree_sets x)) fsets;
        (* val _ = @{print} ((map (Thm.cterm_of lthy)) purefsets); *)

        val id_ons = @{map 6} (fn f => fn bfree_sets => fn bset => fn rel => fn FVarss => fn UFVarss =>
          (* let val _ = @{print} ((0 upto nrecs - 1) ~~ replicate_rec (FVarss ~~ UFVarss)); in *)
          mk_id_on (mk_minus (foldl1 mk_Un (
            bfree_sets @ map_filter (fn (i, (FVars, UFVars)) => 
              if member (op=) (flat rel) i then SOME (mk_UNION (nth rec_sets i $ X)
                 (BNF_FP_Util.mk_case_sum (FVars, UFVars))
              ) else NONE
            ) ((0 upto nrecs - 1) ~~ replicate_rec (FVarss ~~ UFVarss))
          ), bset $ X)) f (* end *)
        ) fs bfree_setss bsets (#binding_relation fp_res) (transpose (map #FVarss (#quotient_fps fp_res)))
          (transpose UFVarsss);

        val binding_rel = map flat (#binding_relation fp_res);

        val rec_boundss = map (fn i =>
          @{map_filter 2} (fn j => fn rel =>
            if member (op=) rel i then SOME j else NONE
          ) (0 upto length binding_rel - 1) binding_rel
        ) (0 upto nrecs - 1);

(*
        val _ = @{print} (#binding_relation fp_res);
        val _ = @{print} (UFVarsss);

        val _ = @{print} (map (Thm.cterm_of lthy) fsets); *)

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
        (*
        val _ = @{print} (map (Thm.cterm_of lthy) UFVarss);
        val _ = @{print} (map (map (Thm.cterm_of lthy)) UFVarsss); *)
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
        (* val _ = @{print} (map (Thm.cterm_of lthy) id_ons); *)

        val _ = @{print} (map (Thm.cterm_of lthy) ufvars_Udtors);

        val Umap_comp =
          let
            val flip = fn f => fn a => fn b => f b a;
            val ap_Umap = flip (fold (flip (curry op$))) Umap;
            val Umap_comp_body_lhs = ap_Umap (fs @ [ap_Umap (gs @ [d])]);
            val Umap_comp_body_rhs = ap_Umap (map2 (curry HOLogic.mk_comp) fs gs) $ d;
          in
            fold_rev Logic.all (fs @ gs @ [d]) (fold_rev (curry Logic.mk_implies)
              (HOLogic.mk_Trueprop (validU $ d) :: f_prems @ g_prems)
              (HOLogic.mk_Trueprop (HOLogic.mk_eq (Umap_comp_body_lhs, Umap_comp_body_rhs)))       
            )
          end

        val _ = @{print} (Thm.cterm_of lthy Umap_comp);
      in [
        (name ^ "_ne", [Udtor_ne]),
        ("alpha_" ^ name, [alpha_Udtor]),
        ("Umap_comp" ^ string_of_int i, [Umap_comp])
      ] end
    ) (1 upto length uTs) (mk_names "Udtor" (1 upto length uTs)) (#pre_mrbnfs fp_res) ds Xs Xs' Umaps UFVarsss Udtors validUs pre_setss (#quotient_fps fp_res);

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

        val names = map (fst o dest_Free);
        val valid_prems = map2 (HOLogic.mk_Trueprop oo curry (op$)) validUs ds;

(*
        val Umap_ids = @{map 4} (fn valid_prem => fn d => fn Umap => fn Umap_cong0 =>
          let val goal = mk_Trueprop_eq (Term.list_comb (Umap, map HOLogic.id_const vars) $ d, d)
          in Goal.prove_sorry lthy (names [d]) [valid_prem] goal (fn {context=ctxt, prems} => EVERY1 [
            (* rtac ctxt Umap_cong0,
               resolve_tac ctxt prems,
               REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound id_apply},
            *)
            K (@{print} prems ; print_tac ctxt "1")
          ]) end
        ) valid_prems ds Umaps (* TODO: Umap_cong0s *) [(), ()];
*)
        val _ = @{print} name

      in (name, Local_Theory.exit_global lthy) end
    ) lthy;
    
  in lthy end

end