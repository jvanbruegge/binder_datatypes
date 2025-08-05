signature MRSBNF_COMP = sig

  val compose_mrsbnfs: BNF_Def.inline_policy -> (theory -> BNF_Def.fact_policy)
    -> (int -> binding -> binding) -> MRSBNF_Def.mrsbnf -> MRSBNF_Def.mrsbnf list
    -> typ list -> typ list list -> typ option list -> typ list list -> ((string * sort) * MRBNF_Def.var_type) list
    -> ((string * sort) list list -> (string * sort) list)
    -> (thm list * (MRBNF_Comp.comp_cache * MRBNF_Comp.unfold_set)) * local_theory
    -> (MRSBNF_Def.mrsbnf * (typ list * typ list)) * ((thm list * (MRBNF_Comp.comp_cache * MRBNF_Comp.unfold_set)) * local_theory)

  val mrsbnf_of_typ: bool -> (theory -> BNF_Def.fact_policy)
    -> (binding -> binding) -> (string * sort) list -> ((string * sort) * MRBNF_Def.var_type) list
    -> ((string * sort) list list -> (string * sort) list)
    -> typ -> (((MRSBNF_Def.mrsbnf Symtab.table * thm list) * (MRBNF_Comp.comp_cache * MRBNF_Comp.unfold_set)) * local_theory)
    -> ((MRSBNF_Def.mrsbnf, MRBNF_Def.mrbnf) MRBNF_Util.either * (typ list * typ list))
        * (((MRSBNF_Def.mrsbnf Symtab.table * thm list) * (MRBNF_Comp.comp_cache * MRBNF_Comp.unfold_set)) * local_theory)

  val seal_mrsbnf: (binding -> binding) -> (thm list * MRBNF_Comp.unfold_set) -> binding
    -> ((string * sort) * MRBNF_Def.var_type) list -> typ list * typ list -> MRSBNF_Def.mrsbnf -> (string * Typedef.info) option -> local_theory
    -> (MRSBNF_Def.mrsbnf * (typ list * MRBNF_Comp.absT_info)) * local_theory

end

structure MRSBNF_Comp : MRSBNF_COMP = struct

open MRBNF_Util

fun mrsbnf_of lthy s = case MRSBNF_Def.mrsbnf_of lthy s of
  SOME mrsbnf => SOME (Inl mrsbnf, lthy)
  | NONE => (case MRBNF_Def.mrbnf_of lthy s of
    SOME mrbnf => SOME (Inr mrbnf, lthy)
    | NONE => Option.map (fn bnf =>
      apfst Inr (MRBNF_Def.register_bnf_as_mrbnf NONE bnf lthy)
    ) (BNF_Def.bnf_of lthy s)
  )

fun is_Inl (Inl _) = true
  | is_Inl _ = false

fun morph_info phi ({rep_type, abs_type, Rep_name: string, Abs_name: string, axiom_name: string}, x) = ({
  rep_type = Morphism.typ phi rep_type,
  abs_type = Morphism.typ phi abs_type,
  Rep_name = Rep_name,
  Abs_name = Abs_name,
  axiom_name = axiom_name
}, x)

fun seal_mrsbnf qualify (bmv_unfolds, mrbnf_unfolds) name Xs tys mrsbnf info_opt lthy =
  let
    val Ds = fst tys;
    val vars = map (TFree o fst) Xs;
    val bmv = MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf;
    val mrbnf' = nth (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf) (BMV_Monad_Def.leader_of_bmv_monad bmv);

    val (_, _, (mrbnfs', (_, lthy))) = MRBNF_Comp.normalize_mrbnfs (K I) [] [map dest_TFree (snd tys)]
      [] Xs (K (map fst Xs)) NONE [mrbnf'] ((MRBNF_Comp.empty_comp_cache, mrbnf_unfolds), lthy);
    val mrbnf' = hd mrbnfs';
    val ((mrbnf, info, (Ds, absT_info)), lthy) = MRBNF_Comp.seal_mrbnf qualify mrbnf_unfolds name true Ds Ds mrbnf' info_opt lthy;

    val var_class = MRBNF_Def.class_of_mrbnf mrbnf;
    val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf';
    val (lives, bounds, frees) = MRBNF_Def.deinterlace (snd tys) var_types;
    val bounds = map (resort_tfree_or_tvar var_class) bounds;
    val frees = map (resort_tfree_or_tvar var_class) frees;
    val rep_T = MRBNF_Def.mk_T_of_mrbnf Ds lives bounds frees mrbnf';

    val (lives', _) = lthy
      |> fold Variable.declare_typ (vars @ map TFree (fold Term.add_tfreesT Ds []))
      |> mk_TFrees (length lives);

    val T = MRBNF_Def.mk_T_of_mrbnf (map TFree (rev (fold_rev Term.add_tfreesT Ds []))) lives bounds frees mrbnf;

    val info = map_prod I (morph_info (MRBNF_Util.subst_typ_morphism (
      (op~~) (apply2 (fn T => map TFree (Term.add_tfreesT T [])) (#abs_type (fst (snd info)), T))
    ))) info;

    val bmv =
      let
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
          (BMV_Monad_Def.leader BMV_Monad_Def.ops_of_bmv_monad bmv, rep_T) Vartab.empty;
        val phi = MRBNF_Util.subst_typ_morphism (
          map (fn (n, (s, T)) => (TVar (n, s), T)
        ) (Vartab.dest tyenv));
        val bmv = BMV_Monad_Def.morph_bmv_monad phi bmv;
        val subst = map2 (fn l => fn l' => (l', nth lives' (find_index (curry (op=) l) lives)))
          (BMV_Monad_Def.leader BMV_Monad_Def.lives_of_bmv_monad bmv)
          (BMV_Monad_Def.leader BMV_Monad_Def.lives'_of_bmv_monad bmv);
      in BMV_Monad_Def.morph_bmv_monad (MRBNF_Util.subst_typ_morphism subst) bmv end;

    val ((bmv, _, bmv_defs, _), lthy) = BMV_Monad_Def.seal_bmv_monad qualify bmv_unfolds name [] bmv (SOME info) lthy;

    val mrbnfs = map_index (fn (i, x) => if i = BMV_Monad_Def.leader_of_bmv_monad bmv then mrbnf else x)
      (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf);

    val mrbnf_defs = #map_unfolds mrbnf_unfolds @ flat (#set_unfoldss mrbnf_unfolds);
    val defs = mrbnf_defs @ bmv_defs @ [MRBNF_Def.map_def_of_mrbnf mrbnf] @ MRBNF_Def.set_defs_of_mrbnf mrbnf;
    val copy = #type_definition (snd (snd info));

    val abs = Term.map_types (Logic.incr_tvar_same 1) (
      Logic.varify_types_global (Const (#Abs_name (fst (snd info)), rep_T --> T))
    );
    val rep = Term.map_types (Logic.incr_tvar_same 1) (
      Logic.varify_types_global (Const (#Rep_name (fst (snd info)), T --> rep_T))
    );

    val mrbnfs = map2 (fn T => fn mrbnf =>
      let
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (MRBNF_Def.T_of_mrbnf mrbnf, T) Vartab.empty;
        val mrbnf = MRBNF_Def.morph_mrbnf (MRBNF_Util.subst_typ_morphism (map (fn (n, (s, T)) => (TVar (n, s), T)) (Vartab.dest tyenv))) mrbnf;
        val subst = map2 (fn l => fn l' => (l', nth lives' (find_index (curry (op=) l) lives)))
          (MRBNF_Def.lives_of_mrbnf mrbnf) (MRBNF_Def.lives'_of_mrbnf mrbnf);
      in MRBNF_Def.morph_mrbnf (MRBNF_Util.subst_typ_morphism subst) mrbnf end
    ) (BMV_Monad_Def.ops_of_bmv_monad bmv) mrbnfs;

    val subst = Term.subst_atomic_types (lives ~~ lives');
    val unfold_defs = Local_Defs.unfold lthy mrbnf_defs;

    val comp_assocs = [
      infer_instantiate' lthy [SOME (Thm.cterm_of lthy (subst abs))] @{thm comp_assoc},
      infer_instantiate' lthy [NONE, SOME (Thm.cterm_of lthy (subst rep))] @{thm comp_assoc}
    ];
    val comp_applys = [
      infer_instantiate' lthy [SOME (Thm.cterm_of lthy (subst abs))] @{thm comp_apply},
      infer_instantiate' lthy [NONE, SOME (Thm.cterm_of lthy (subst rep))] @{thm comp_apply}
    ];

    val (mrsbnf, lthy) = MRSBNF_Def.mrsbnf_def (K BNF_Def.Note_Some) qualify NONE mrbnfs bmv
      (map_index (fn (i, axioms) => if i <> BMV_Monad_Def.leader_of_bmv_monad bmv then {
        map_Sb = Option.map (fn thm => fn ctxt => HEADGOAL (rtac ctxt thm THEN_ALL_NEW assume_tac ctxt)) (#map_Sb axioms),  
        map_Injs = Option.map (map (fn thm => fn ctxt => HEADGOAL (rtac ctxt thm THEN_ALL_NEW assume_tac ctxt))) (#map_Injs axioms),
        map_is_Sb = fn ctxt => HEADGOAL (rtac ctxt (#map_is_Sb axioms) THEN_ALL_NEW assume_tac ctxt),
        set_Sb = map (fn thm => fn ctxt => HEADGOAL (rtac ctxt thm THEN_ALL_NEW assume_tac ctxt)) (#set_Sb axioms),
        set_Vrs = map (fn thm => fn ctxt => rtac ctxt thm 1) (#set_Vrs axioms)
      } else {
        map_Sb = Option.map (fn thm => fn ctxt => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (defs @ [@{thm SSupp_type_copy} OF [copy]])),
          rtac ctxt @{thm type_copy_Map_Sb},
          rtac ctxt copy,
          rtac ctxt copy,
          K (Local_Defs.unfold0_tac ctxt (comp_assocs @ [@{thm type_copy_Rep_o_Abs_o} OF [copy]])),
          rtac ctxt (unfold_defs thm) THEN_ALL_NEW assume_tac ctxt
        ]) (#map_Sb axioms),  
        map_Injs = Option.map (map (fn thm => fn ctxt => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt defs),
          REPEAT_DETERM o rtac ctxt @{thm trans[OF comp_assoc]},
          rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
          K (Local_Defs.unfold0_tac ctxt [@{thm type_copy_Rep_o_Abs_o} OF [copy]]),
          rtac ctxt (unfold_defs thm) THEN_ALL_NEW assume_tac ctxt
        ])) (#map_Injs axioms),
        map_is_Sb = fn ctxt => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (defs @ [@{thm SSupp_type_copy} OF [copy]])),
          resolve_tac ctxt @{thms type_copy_map_comp0 type_copy_map_cong0},
          rtac ctxt copy,
          K (Local_Defs.unfold0_tac ctxt (comp_assocs @ [@{thm type_copy_Rep_o_Abs_o} OF [copy]])),
          rtac ctxt (unfold_defs (#map_is_Sb axioms)) THEN_ALL_NEW assume_tac ctxt
        ],
        set_Sb = map (fn _ => fn ctxt => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (defs @ [@{thm SSupp_type_copy} OF [copy]])),
          K (Local_Defs.unfold0_tac ctxt (comp_applys @ [#Abs_inverse (snd (snd info)) OF @{thms UNIV_I}])),
          rtac ctxt trans,
          resolve_tac ctxt (map unfold_defs (#set_Sb axioms)),
          REPEAT_DETERM o assume_tac ctxt,
          K (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
          rtac ctxt refl
        ]) (#set_Sb axioms),
        set_Vrs = map (fn thm => fn ctxt => EVERY1 [
          K (Local_Defs.unfold_tac ctxt (defs @ [@{thm SSupp_type_copy} OF [copy]])),
          rtac ctxt @{thm trans[OF comp_apply]},
          rtac ctxt trans,
          rtac ctxt (unfold_defs thm),
          K (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
          rtac ctxt refl
        ]) (#set_Vrs axioms)
      }
    ) (MRSBNF_Def.axioms_of_mrsbnf mrsbnf)) lthy;
  in ((mrsbnf, (snd (dest_Type T), absT_info)), lthy) end

fun compose_mrsbnfs inline_policy fact_policy qualify outer inners oDs Dss oAs Ass Xs flatten_tyargs ((old_bmv_unfold, accum), lthy) =
  let
    val outer_bmv = MRSBNF_Def.bmv_monad_of_mrsbnf outer;

    fun separate_vars vars Ds mrsbnf =
      let
        val bmv = MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf;
        val mrbnfs = MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf;
        val mrbnf = nth mrbnfs (BMV_Monad_Def.leader_of_bmv_monad bmv);
        val (lives, bounds, frees) = MRBNF_Def.deinterlace vars (MRBNF_Def.var_types_of_mrbnf mrbnf);

        val bounds = map_filter (Option.map (resort_tfree_or_tvar @{sort var})) bounds;
        val frees = map_filter (Option.map (resort_tfree_or_tvar @{sort var})) frees;
        
        val lives' = case lives of
          NONE::_ => replicate (length lives) @{typ unit}
          | _ => map_filter I lives

        val T = MRBNF_Def.mk_T_of_mrbnf Ds lives' bounds frees mrbnf;

        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
          (BMV_Monad_Def.leader BMV_Monad_Def.ops_of_bmv_monad bmv, T) Vartab.empty;
        val phi = MRBNF_Util.subst_typ_morphism (map (fn (x, (s, T)) => (TVar (x, s), T)) (Vartab.dest tyenv));
        val bmv = BMV_Monad_Def.morph_bmv_monad phi bmv;
      in {
        frees = BMV_Monad_Def.leader BMV_Monad_Def.frees_of_bmv_monad bmv,
        deads = BMV_Monad_Def.leader BMV_Monad_Def.deads_of_bmv_monad bmv,
        lives = BMV_Monad_Def.leader BMV_Monad_Def.lives_of_bmv_monad bmv
      } end;

    val oAs' = let val x = separate_vars oAs oDs outer in { frees = #frees x, deads = #deads x } end;
    val Ass' = @{map 3} (separate_vars o map SOME) Ass Dss inners;

    val ((bmv, bmv_unfolds), lthy) = BMV_Monad_Def.compose_bmv_monad (qualify 0) (MRSBNF_Def.bmv_monad_of_mrsbnf outer)
      (map (Inl o MRSBNF_Def.bmv_monad_of_mrsbnf) inners) oAs' (map SOME Ass') lthy;

    val leader = BMV_Monad_Def.leader_of_bmv_monad outer_bmv;
    val outer_mrbnf = nth (MRSBNF_Def.mrbnfs_of_mrsbnf outer) leader;
    val inner_mrbnfs = map (fn mrsbnf => nth (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf) leader) inners;

    val ((mrbnf, tys), (mrbnf_unfolds, lthy)) = MRBNF_Comp.compose_mrbnf MRBNF_Def.Smart_Inline
      qualify flatten_tyargs outer_mrbnf inner_mrbnfs oDs Dss oAs Ass Xs (accum, lthy);

    val mrbnf =
      let
        val T = hd (BMV_Monad_Def.ops_of_bmv_monad bmv);
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (MRBNF_Def.T_of_mrbnf mrbnf, T) Vartab.empty;
        val phi = MRBNF_Util.subst_typ_morphism (map (fn (x, (s, T)) => (TVar (x, s), T)) (Vartab.dest tyenv));
      in MRBNF_Def.morph_mrbnf phi mrbnf end

    val (mrbnfs, axioms') = split_list ((mrbnf, NONE) :: maps (fn mrsbnf =>
      let
        val mrbnfs = MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf;
        fun find_match mrbnf T = case T of
          T as Type _ => map_filter (fn T' => Option.map (fn tyenv =>
            MRBNF_Def.morph_mrbnf (MRBNF_Util.subst_typ_morphism (
              map (fn (x, (s, T)) => (TVar (x, s), T)) (Vartab.dest tyenv)
            )) mrbnf
          ) (try (Sign.typ_match (Proof_Context.theory_of lthy) (T, T')) Vartab.empty))
            (BMV_Monad_Def.ops_of_bmv_monad bmv)
          | _ => []
      in @{map_filter 2} (fn mrbnf => fn i => case find_match mrbnf (MRBNF_Def.T_of_mrbnf mrbnf) of
        [] => NONE | x::_ => SOME (x, SOME (nth (MRSBNF_Def.axioms_of_mrsbnf mrsbnf) i))
      ) mrbnfs (0 upto length mrbnfs - 1) end
    ) inners);
    val (mrbnfs, axioms') = split_list (distinct ((op=) o apply2 (MRBNF_Def.T_of_mrbnf o fst)) (mrbnfs ~~ axioms'));

    val mrbnfs = map (fn mrbnf =>
      let
        val leader = BMV_Monad_Def.leader_of_bmv_monad bmv;
        val lives = nth (BMV_Monad_Def.lives_of_bmv_monad bmv) leader;
        val lives' = nth (BMV_Monad_Def.lives'_of_bmv_monad bmv) leader;
        val subst = map2 (fn l => fn l' => (l', nth lives' (find_index (curry (op=) l) lives)))
          (MRBNF_Def.lives_of_mrbnf mrbnf) (MRBNF_Def.lives'_of_mrbnf mrbnf);
      in MRBNF_Def.morph_mrbnf (MRBNF_Util.subst_typ_morphism subst) mrbnf end
    ) mrbnfs;

    val no_reflexive = filter_out (fn thm => case try (HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm of
      NONE => false | SOME (lhs, rhs) => lhs = rhs
    );

    val (mrsbnf, lthy) = MRSBNF_Def.mrsbnf_def fact_policy (qualify 0 o @{print warning}) NONE mrbnfs bmv
      (map (fn axioms => case axioms of SOME axioms => {
        map_Sb = Option.map (fn thm => fn ctxt => HEADGOAL (rtac ctxt thm THEN_ALL_NEW assume_tac ctxt)) (#map_Sb axioms),  
        map_Injs = Option.map (map (fn thm => fn ctxt => HEADGOAL (rtac ctxt thm THEN_ALL_NEW assume_tac ctxt))) (#map_Injs axioms),
        map_is_Sb = fn ctxt => HEADGOAL (rtac ctxt (#map_is_Sb axioms) THEN_ALL_NEW assume_tac ctxt),
        set_Sb = map (fn thm => fn ctxt => HEADGOAL (rtac ctxt thm THEN_ALL_NEW assume_tac ctxt)) (#set_Sb axioms),
        set_Vrs = map (fn thm => fn ctxt => rtac ctxt thm 1) (#set_Vrs axioms)
      } | NONE => {
        map_Sb = if MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.live_of_mrbnf mrbnf - length (BMV_Monad_Def.leader BMV_Monad_Def.frees_of_bmv_monad bmv) > 0 then
          SOME (fn ctxt => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt (bmv_unfolds @ #map_unfolds (snd mrbnf_unfolds))),
            rtac ctxt trans,
            TRY o EVERY' [
              rtac ctxt @{thm trans[OF comp_assoc[symmetric]]},
              rtac ctxt trans,
              rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
              resolve_tac ctxt (map_filter #map_Sb (MRSBNF_Def.axioms_of_mrsbnf outer)),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' rtac ctxt @{thm SSupp_Inj_bound}),
              rtac ctxt @{thm trans[OF comp_assoc]},
              rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]}
            ],
            SELECT_GOAL (Local_Defs.unfold0_tac ctxt (no_reflexive (map_filter #Map_map (MRSBNF_Def.facts_of_mrsbnf outer)))),
            rtac ctxt (MRBNF_Def.map_comp0_of_mrbnf outer_mrbnf RS sym),
            REPEAT_DETERM o rtac ctxt @{thm supp_id_bound},
            K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
            rtac ctxt sym,
            rtac ctxt trans,
            TRY o EVERY' [
              rtac ctxt @{thm trans[OF comp_assoc]},
              rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]}
            ],
            SELECT_GOAL (Local_Defs.unfold0_tac ctxt (no_reflexive (map_filter #Map_map (MRSBNF_Def.facts_of_mrsbnf outer)))),
            rtac ctxt (MRBNF_Def.map_comp0_of_mrbnf outer_mrbnf RS sym),
            REPEAT_DETERM o rtac ctxt @{thm supp_id_bound},
            K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
            TRY o EVERY' [
              rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<circ>)"]},
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt (
                map (fn thm => thm RS sym) (no_reflexive (map_filter #Map_map (MRSBNF_Def.facts_of_mrsbnf outer)))
                @ flat (map_filter (Option.map #Map_Injs) (BMV_Monad_Def.params_of_bmv_monad outer_bmv))
              )),
              rtac ctxt refl
            ],
            rtac ctxt sym,
            rtac ctxt ext,
            rtac ctxt (MRBNF_Def.map_cong0_of_mrbnf outer_mrbnf),
            REPEAT_DETERM o rtac ctxt @{thm supp_id_bound},
            K (Local_Defs.unfold0_tac ctxt (@{thms id_o o_id} @ no_reflexive (maps (map MRBNF_Def.map_id0_of_mrbnf o MRSBNF_Def.mrbnfs_of_mrsbnf) inners))),
            REPEAT_DETERM o FIRST' (rtac ctxt refl :: map (fn inner => EVERY' [
              resolve_tac ctxt (map (Local_Defs.unfold0 ctxt (
                no_reflexive (maps (map MRBNF_Def.map_id0_of_mrbnf o MRSBNF_Def.mrbnfs_of_mrsbnf) inners)
              )) (map_filter (Option.map (fn thm => Local_Defs.unfold0 ctxt (bmv_unfolds @ #map_unfolds (snd mrbnf_unfolds))
                (thm RS fun_cong)
              ) o #map_Sb) (MRSBNF_Def.axioms_of_mrsbnf inner))),
              REPEAT_DETERM o assume_tac ctxt
            ]) inners)
          ]) else NONE,
        map_is_Sb = fn ctxt => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (bmv_unfolds @ #map_unfolds (snd mrbnf_unfolds))),
          rtac ctxt trans,
          resolve_tac ctxt (map #map_is_Sb (MRSBNF_Def.axioms_of_mrsbnf outer)),
          REPEAT_DETERM o (assume_tac ctxt ORELSE' rtac ctxt @{thm supp_id_bound}),
          K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
          rtac ctxt sym,
          TRY o EVERY' [
            rtac ctxt @{thm trans[OF comp_assoc]},
            rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]}
          ],
          rtac ctxt trans,
          resolve_tac ctxt (map_filter (Option.map (#Map_comp o #axioms)) (BMV_Monad_Def.params_of_bmv_monad outer_bmv)),
          K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
          rtac ctxt ext,
          rtac ctxt sym,
          resolve_tac ctxt (map_filter (Option.map (#Map_cong o #axioms)) (BMV_Monad_Def.params_of_bmv_monad outer_bmv)),
          EVERY' (map (fn inner => FIRST' [
            SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms id_bnf_apply}) THEN' rtac ctxt refl,
            EVERY' [
              resolve_tac ctxt (map (fn ax => Local_Defs.unfold0 ctxt (@{thms id_o o_id id_bnf_apply} @ bmv_unfolds @ #map_unfolds (snd mrbnf_unfolds))
                (#map_is_Sb ax RS fun_cong)
              ) (MRSBNF_Def.axioms_of_mrsbnf inner)),
              REPEAT_DETERM o assume_tac ctxt
            ]
          ]) inners)
        ],
        map_Injs = if MRBNF_Def.bound_of_mrbnf mrbnf = 0 then NONE else SOME (map_filter (fn Inj =>
          if body_type (fastype_of Inj) <> MRBNF_Def.T_of_mrbnf mrbnf then NONE else SOME (fn ctxt => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt (bmv_unfolds @ #map_unfolds (snd mrbnf_unfolds) @ flat (#set_unfoldss (snd mrbnf_unfolds)))),
            if MRBNF_Def.bound_of_mrbnf outer_mrbnf = 0 then K all_tac else
            let val thm = Local_Defs.unfold0 ctxt @{thms id_o o_id} (
              infer_instantiate' ctxt (map (Option.map (fn t =>
                let
                  val t' = case t of
                    Const (@{const_name id}, Type ("fun", [TVar ((n, i), s), _])) =>
                      HOLogic.id_const (TVar ((n, i+1), s))
                    | t => t
                in Thm.cterm_of lthy t' end
              )) (flat (MRBNF_Def.interlace (replicate (MRBNF_Def.live_of_mrbnf outer_mrbnf) [])
                  (replicate (MRBNF_Def.bound_of_mrbnf outer_mrbnf) [NONE])
                  (map (single o SOME o HOLogic.id_const) (MRBNF_Def.frees_of_mrbnf outer_mrbnf))
                  (MRBNF_Def.var_types_of_mrbnf outer_mrbnf)
                ) @ flat (MRBNF_Def.interlace (replicate (MRBNF_Def.live_of_mrbnf outer_mrbnf) [])
                  (map (single o SOME o  HOLogic.id_const) (MRBNF_Def.bounds_of_mrbnf outer_mrbnf))
                  (replicate (MRBNF_Def.free_of_mrbnf outer_mrbnf) [NONE])
                  (MRBNF_Def.var_types_of_mrbnf outer_mrbnf)
                ) @ maps (fn a => [NONE, SOME (HOLogic.id_const a)]) (MRBNF_Def.lives_of_mrbnf outer_mrbnf)
              )) (MRBNF_Def.map_comp0_of_mrbnf outer_mrbnf)
            );
            in EVERY' [
              rtac ctxt trans,
              rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
              rtac ctxt thm,
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
              rtac ctxt trans,
              rtac ctxt @{thm trans[OF comp_assoc]},
              rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
              resolve_tac ctxt (maps (the_default [] o #map_Injs) (MRSBNF_Def.axioms_of_mrsbnf outer)),
              REPEAT_DETERM o assume_tac ctxt
            ] end,
            K (Local_Defs.unfold0_tac ctxt (map (fn ax => the (#Map_map ax) RS sym) (MRSBNF_Def.facts_of_mrsbnf outer))),
            resolve_tac ctxt (flat (map_filter (Option.map #Map_Injs) (BMV_Monad_Def.params_of_bmv_monad outer_bmv)))
          ])
        ) (hd (BMV_Monad_Def.Injs_of_bmv_monad bmv))),
        set_Sb = replicate (MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.live_of_mrbnf mrbnf) (fn ctxt => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (bmv_unfolds @ #map_unfolds (snd mrbnf_unfolds) @ flat (#set_unfoldss (snd mrbnf_unfolds)))),
          SUBGOAL (fn (goal, _) =>
            let
              val outer_set_maps = @{map_filter 2} (fn MRBNF_Def.Live_Var => SOME | _ => K NONE) (MRBNF_Def.var_types_of_mrbnf outer_mrbnf) (MRBNF_Def.set_map_of_mrbnf outer_mrbnf);
              fun strip_all (Const (@{const_name Pure.all}, _) $ Abs (x, T, t)) = apfst (cons (x, T)) (strip_all t)
                | strip_all t = ([], t)
              val T = snd (snd (split_last (fst (strip_all goal))))
              val thms = map (fn thm =>
                let
                  val arg = Var (hd (Term.add_vars (Thm.prop_of thm) []));
                  val tyenv = Sign.typ_match (Proof_Context.theory_of ctxt)
                    (fastype_of arg, T) Vartab.empty;
                  val insts = map (fn (x, (s, T)) => ((x, s), Thm.ctyp_of ctxt T)) (Vartab.dest tyenv)
                in instantiate_normalize (TVars.make insts, Vars.empty) thm end
              ) outer_set_maps;
              val comp_apply =
                let
                  val thm = @{thm comp_apply};
                  val arg = Var (hd (rev (Term.add_vars (Thm.prop_of thm) [])));
                  val tyenv = Sign.typ_match (Proof_Context.theory_of ctxt)
                    (fastype_of arg, T --> T) Vartab.empty;
                  val insts = map (fn (x, (s, T)) => ((x, s), Thm.ctyp_of ctxt T)) (Vartab.dest tyenv)
                in instantiate_normalize (TVars.make insts, Vars.empty) thm end
            in EVERY1 [
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] thms,
                REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
              ],
              K (Local_Defs.unfold0_tac ctxt (comp_apply :: @{thms UN_empty2 Un_empty_right Un_empty_left image_id})),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] (maps #set_Sb (MRSBNF_Def.axioms_of_mrsbnf outer)),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' rtac ctxt @{thm SSupp_Inj_bound})
              ],
              K (Local_Defs.unfold0_tac ctxt (#Vrs_Map (the (BMV_Monad_Def.leader BMV_Monad_Def.params_of_bmv_monad outer_bmv)))),
              K (Local_Defs.unfold0_tac ctxt (no_reflexive (map_filter #Map_map (MRSBNF_Def.facts_of_mrsbnf outer)))),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] thms,
                REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
              ],
              K (Local_Defs.unfold0_tac ctxt @{thms image_comp[unfolded comp_def] image_Un}),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] (maps (maps (map (
                  Local_Defs.unfold0 ctxt (flat (#set_unfoldss (snd mrbnf_unfolds)))
                ) o #set_Sb) o MRSBNF_Def.axioms_of_mrsbnf) inners),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' rtac ctxt @{thm SSupp_Inj_bound})
              ],
              K (Local_Defs.unfold_tac ctxt (
                @{thms Un_Union_image Union_Un_distrib UN_UN_flatten UN_empty UN_empty2 Un_empty_left Un_empty_right}
                @ flat (maps #set_Injs (MRSBNF_Def.facts_of_mrsbnf outer))
                @ flat (maps #Supp_Injss (BMV_Monad_Def.facts_of_bmv_monad outer_bmv))
              ))
            ] end
          ),
          rtac ctxt refl ORELSE' EVERY' [
            rtac ctxt @{thm set_eqI},
            K (Local_Defs.unfold0_tac ctxt @{thms Un_assoc[symmetric]}),
            K (Local_Defs.unfold0_tac ctxt @{thms Un_iff}),
            rtac ctxt iffI,
            REPEAT_DETERM_N 2 o EVERY' [
              rotate_tac ~1,
              etac ctxt @{thm contrapos_pp},
              K (Local_Defs.unfold0_tac ctxt @{thms de_Morgan_disj}),
              REPEAT_DETERM o etac ctxt conjE,
              REPEAT_DETERM o rtac ctxt conjI,
              REPEAT_DETERM o assume_tac ctxt
            ]
          ]
        ]),
        set_Vrs = replicate (length (BMV_Monad_Def.leader BMV_Monad_Def.frees_of_bmv_monad bmv)) (fn ctxt => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (bmv_unfolds @ #map_unfolds (snd mrbnf_unfolds) @ flat (#set_unfoldss (snd mrbnf_unfolds)))),
          SUBGOAL (fn (goal, _) =>
            let
              val outer_set_maps = @{map_filter 2} (fn MRBNF_Def.Live_Var => SOME | _ => K NONE) (MRBNF_Def.var_types_of_mrbnf outer_mrbnf) (MRBNF_Def.set_map_of_mrbnf outer_mrbnf);
              fun strip_all (Const (@{const_name Pure.all}, _) $ Abs (x, T, t)) = apfst (cons (x, T)) (strip_all t)
                | strip_all t = ([], t)
              val T = snd (snd (split_last (fst (strip_all goal))))
              val thms = map (fn thm =>
                let
                  val arg = Var (hd (Term.add_vars (Thm.prop_of thm) []));
                  val tyenv = Sign.typ_match (Proof_Context.theory_of ctxt)
                    (fastype_of arg, T) Vartab.empty;
                  val insts = map (fn (x, (s, T)) => ((x, s), Thm.ctyp_of ctxt T)) (Vartab.dest tyenv)
                in instantiate_normalize (TVars.make insts, Vars.empty) thm end
              ) outer_set_maps;
            in REPEAT_DETERM (EVERY1 [
              EqSubst.eqsubst_tac ctxt [0] thms,
              REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
            ]) end
          ),
          K (Local_Defs.unfold_tac ctxt (@{thms UN_empty2 Un_empty_right Un_empty_left image_id
            Un_assoc[symmetric] Un_Union_image UN_singleton Un_absorb
          } @ no_reflexive (map (Local_Defs.unfold0 ctxt (
              flat (#set_unfoldss (snd mrbnf_unfolds))
            )) (flat (maps (map #set_Vrs o MRSBNF_Def.axioms_of_mrsbnf) inners)))
          )),
          rtac ctxt refl
        ])
      }) axioms') lthy;
  in ((mrsbnf, tys), ((old_bmv_unfold @ bmv_unfolds, mrbnf_unfolds), lthy)) end

fun mrsbnf_of_typ _ _ qualify Ds0 var_types _ (T as TFree T') (accum:((MRSBNF_Def.mrsbnf Symtab.table * thm list) * (MRBNF_Comp.comp_cache * MRBNF_Comp.unfold_set)), lthy:local_theory) =
  (if member (op =) Ds0 T' then ((Inr MRBNF_Comp.DEADID_mrbnf, ([T], [])), (accum, lthy)) else
      (case map_filter (fn a => if fst a = T' then SOME (snd a) else NONE) var_types of
        [] => ((Inr MRBNF_Comp.ID_mrbnf, ([], [T])), (accum, lthy))
        | [MRBNF_Def.Dead_Var] => error "var_types may only be Live, Free or Bound, use Ds0 for deads"
        | [var_type] =>
          let
            val qualify' = qualify o Binding.suffix_name ("_" ^ fst T')
            val (ID', accum') = MRBNF_Comp.demote_mrbnf qualify' [var_type] MRBNF_Comp.ID_mrbnf (snd accum, lthy)
          in ((Inr ID', ([], [T])), ((fst accum, fst accum'), snd accum')) end
        | _ => error "Same variable appears twice in var_types"
      )
    )
  | mrsbnf_of_typ _ _ _ _ _ _ (TVar _) _ = error "unexpected schematic variable"
  | mrsbnf_of_typ optim const_policy qualify' Ds0 var_types flatten_tyargs (T as Type (n, Ts)) (((mrsbnf_cache, (bmv_unfolds:thm list)), accum), lthy) = (case mrsbnf_of lthy n of
    NONE => ((Inr MRBNF_Comp.DEADID_mrbnf, ([T], [])), (((mrsbnf_cache, bmv_unfolds), accum), lthy))
    | SOME (outer, lthy) =>
      if optim andalso forall is_TFree Ts andalso length Ts = length (subtract (op=) Ds0 (Term.add_tfreesT T [])) then
        let
          val mrbnf = case outer of
            Inl mrsbnf => nth (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf) (BMV_Monad_Def.leader_of_bmv_monad (MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf))
            | Inr mrbnf => mrbnf;
          val phi = MRBNF_Util.subst_typ_morphism (
            snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf)) ~~ Ts
          );
          val mrbnf' = MRBNF_Def.morph_mrbnf phi mrbnf;
          val deads = MRBNF_Def.deads_of_mrbnf mrbnf';
          val _ = case filter (Option.isSome o AList.lookup (op=) var_types o dest_TFree) deads of
            T'::_ => error ("Variable " ^ Syntax.string_of_typ lthy T' ^ " is forced dead by type " ^ Syntax.string_of_typ lthy T ^ " but was specified as other usage")
            | [] => ()
          val Ts' = subtract (op=) deads Ts;

          val var_types = map (AList.lookup (op=) var_types o dest_TFree) Ts';
          val var_types = @{map 3} (fn req => fn var_type => fn T => if member (op=) Ds0 (dest_TFree T) then
            MRBNF_Def.Dead_Var else the_default var_type req
          ) var_types (MRBNF_Def.var_types_of_mrbnf mrbnf) Ts';

          val (mrsbnf, accum) = if MRBNF_Def.var_types_of_mrbnf mrbnf = var_types then
              (outer, ((bmv_unfolds, accum), lthy))
            else case outer of
              Inl mrsbnf => error "TODO: Demote MRSBNF"
              | Inr mrbnf => apsnd (apfst (pair bmv_unfolds)) (apfst Inr (MRBNF_Comp.demote_mrbnf qualify' var_types mrbnf (accum, lthy)));
        in ((mrsbnf, (inter (op=) Ts (deads @ map TFree Ds0), subtract (op=) (map TFree Ds0) Ts')), apfst (apfst (pair mrsbnf_cache)) accum) end
      else
        let
          val name = Long_Name.base_name n;
          fun qualify i =
            let val namei = name ^ nonzero_string_of_int i;
            in qualify' o Binding.qualify true namei end;
          val mrbnf = case outer of
            Inl mrsbnf => hd (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf)
            | Inr mrbnf => mrbnf

          val odead = MRBNF_Def.dead_of_mrbnf mrbnf;
          val olive = MRBNF_Def.live_of_mrbnf mrbnf;
          val obound = MRBNF_Def.bound_of_mrbnf mrbnf;
          val ofree = MRBNF_Def.free_of_mrbnf mrbnf;
          val Ds = map (fn i => TFree (string_of_int i, [])) (1 upto odead);
          val Us = snd (Term.dest_Type (MRBNF_Def.mk_T_of_mrbnf Ds (replicate olive dummyT) (replicate obound dummyT) (replicate ofree dummyT) mrbnf));
          val oDs_pos = map (fn x => find_index (fn y => x = y) Us) Ds
            |> filter (fn x => x >= 0);
          val oAs = map (fn (T, var_type) => case var_type of
            MRBNF_Def.Live_Var => NONE | _ => SOME T
          ) (Ts ~~ MRBNF_Def.var_types_of_mrbnf mrbnf)
          val oDs = map (nth Ts) oDs_pos;
          val ofree_bound_pos = map_filter I (map_index (fn (i, x) => case x of
            SOME _ => SOME i | NONE => NONE
          ) oAs)
          val Ts' = map (nth Ts) (subtract (op =) (oDs_pos @ ofree_bound_pos) (0 upto length Ts - 1));

          val ((inners, (Dss, Ass)), (((mrsbnf_cache, bmv_unfolds:thm list), accum), lthy)) =
            apfst (apsnd split_list o split_list) (@{fold_map 2}
              (fn i => mrsbnf_of_typ optim const_policy (qualify i) Ds0 var_types flatten_tyargs)
              (1 upto length Ts') Ts' (((mrsbnf_cache, bmv_unfolds), accum), lthy));

          val Xs = rev (Term.add_tfreesT T []);
          val Xs' = map (swap o `(the_default MRBNF_Def.Live_Var o AList.lookup (op=) var_types)) Xs

        in if exists is_Inl inners orelse is_Inl outer then
          let
            fun upgrade_mrbnf mrbnf (mrsbnf_cache, lthy) =
              let
                val T = MRBNF_Def.T_of_mrbnf mrbnf;
                fun is_leaf (Type (_, Ts)) = forall Term.is_TVar Ts
                  | is_leaf (TVar _) = true
                  | is_leaf _ = false
                val name = Binding.name_of (MRBNF_Def.name_of_mrbnf mrbnf);
              in if not (is_leaf T) then
                 let
                    val (mrsbnf, lthy) = MRSBNF_Def.mrsbnf_of_mrbnf mrbnf lthy;
                    val mrsbnf_cache = Symtab.insert (K true) (name, mrsbnf) mrsbnf_cache;
                  in (mrsbnf, (mrsbnf_cache, lthy)) end
                else case MRSBNF_Def.mrsbnf_of lthy name of
                SOME mrsbnf => (mrsbnf, (mrsbnf_cache, lthy))
                | NONE => (case Symtab.lookup mrsbnf_cache name of
                  SOME mrsbnf => (mrsbnf, (mrsbnf_cache, lthy))
                  | NONE =>
                    let
                      val (mrsbnf, lthy) = MRSBNF_Def.mrsbnf_of_mrbnf mrbnf lthy;
                      val mrsbnf_cache = Symtab.insert (K true) (name, mrsbnf) mrsbnf_cache;
                    in (mrsbnf, (mrsbnf_cache, lthy)) end
                  )
              end

            val (outer', (mrsbnf_cache, lthy)) = case outer of
              Inl mrsbnf => (mrsbnf, (mrsbnf_cache, lthy))
              | Inr mrbnf => upgrade_mrbnf mrbnf (mrsbnf_cache, lthy)
            val (inners', (mrsbnf_cache, lthy)) = fold_map (fn Inl mrsbnf => pair mrsbnf
              | Inr mrbnf => upgrade_mrbnf mrbnf
            ) inners (mrsbnf_cache, lthy);

            val unfolds' = bmv_unfolds @ maps (BMV_Monad_Def.unfolds_of_bmv_monad o MRSBNF_Def.bmv_monad_of_mrsbnf) (outer' :: inners');

            val ((mrsbnf, tys), ((unfolds, accum), lthy)) = compose_mrsbnfs BNF_Def.Smart_Inline const_policy qualify outer' inners'
              oDs Dss oAs Ass Xs' flatten_tyargs ((bmv_unfolds, accum), lthy);
          in ((Inl mrsbnf, tys), (((mrsbnf_cache, unfolds' @ unfolds), accum), lthy)) end
        else
          (apsnd (apfst (pair (mrsbnf_cache, bmv_unfolds))) (apfst (apfst Inr) (MRBNF_Comp.compose_mrbnf MRBNF_Def.Smart_Inline qualify (distinct (op=) o flat)
            mrbnf (map (fn Inr x => x | _ => error "impossible") inners) oDs Dss oAs Ass Xs' (accum, lthy)
          )))
        end
    );

end