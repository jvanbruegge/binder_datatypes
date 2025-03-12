signature MRSBNF_DEF = sig
  type mrsbnf

  type 'a mrsbnf_axioms = {
    map_is_Sb: 'a,
    set_Vrs: 'a list,
    map_Sb: 'a option,
    set_Sb: 'a list
  };

  type mrsbnf_facts = {
    SSupp_map_subset: thm option list,
    SSupp_map_bound: thm option list,
    map_Inj: thm option list,
    Sb_comp_right: thm,
    map_Sb_strong: thm
  };

  val id_bmv_monad: BMV_Monad_Def.bmv_monad
  val mk_id_bmv_monad: string * sort -> BMV_Monad_Def.bmv_monad

  val bmv_monad_of_mrsbnf: mrsbnf -> BMV_Monad_Def.bmv_monad
  val mrbnfs_of_mrsbnf: mrsbnf -> MRBNF_Def.mrbnf list
  val axioms_of_mrsbnf: mrsbnf -> thm mrsbnf_axioms list
  val facts_of_mrsbnf: mrsbnf -> mrsbnf_facts list

  val morph_mrsbnf: morphism -> mrsbnf -> mrsbnf

  val mrsbnf_def: (theory -> BNF_Def.fact_policy) -> (binding -> binding) -> string option
    -> MRBNF_Def.mrbnf list -> BMV_Monad_Def.bmv_monad -> (Proof.context -> tactic) mrsbnf_axioms list
    -> local_theory -> mrsbnf * local_theory

  val register_mrsbnf: string -> mrsbnf -> local_theory -> local_theory;
  val mrsbnf_of_generic: Context.generic -> string -> mrsbnf option;
  val mrsbnf_of: Proof.context -> string -> mrsbnf option;

  val pbmv_monad_of_typ: bool -> BNF_Def.inline_policy -> (theory -> BNF_Def.fact_policy)
    -> (string * sort) list -> (binding -> binding) -> typ -> (thm list * local_theory)
    -> BMV_Monad_Def.bmv_monad option * (thm list * local_theory)
end

structure MRSBNF_Def : MRSBNF_DEF = struct

open MRBNF_Util

type 'a mrsbnf_axioms = {
  map_is_Sb: 'a,
  set_Vrs: 'a list,
  map_Sb: 'a option,
  set_Sb: 'a list
}

fun map_mrsbnf_axioms (f:'a -> 'b) ({ map_is_Sb, set_Vrs, map_Sb, set_Sb }: 'a mrsbnf_axioms) = {
  map_is_Sb = f map_is_Sb,
  set_Vrs = map f set_Vrs,
  map_Sb = Option.map f map_Sb,
  set_Sb = map f set_Sb
}: 'b mrsbnf_axioms;

val morph_mrsbnf_axioms = map_mrsbnf_axioms o Morphism.thm

fun apply_mrsbnf_axioms ({
  map_is_Sb=f1, map_Sb=f2, set_Sb=f3s, set_Vrs=f4s
}: ('a -> 'b) mrsbnf_axioms) ({
  map_is_Sb, map_Sb, set_Sb, set_Vrs
}: 'a mrsbnf_axioms) = {
  map_is_Sb = f1 map_is_Sb,
  map_Sb = Option.map (fn t => the f2 t) map_Sb,
  set_Sb = map2 (curry (op|>)) set_Sb f3s,
  set_Vrs = map2 (curry (op|>)) set_Vrs f4s
}: 'b mrsbnf_axioms

type mrsbnf_facts = {
  SSupp_map_subset: thm option list,
  SSupp_map_bound: thm option list,
  map_Inj: thm option list,
  Sb_comp_right: thm,
  map_Sb_strong: thm
}

fun morph_mrsbnf_facts phi ({
    SSupp_map_subset, SSupp_map_bound, map_Inj, Sb_comp_right, map_Sb_strong
}: mrsbnf_facts) = {
  SSupp_map_subset = map (Option.map (Morphism.thm phi)) SSupp_map_subset,
  SSupp_map_bound = map (Option.map (Morphism.thm phi)) SSupp_map_bound,
  map_Inj = map (Option.map (Morphism.thm phi)) map_Inj,
  Sb_comp_right = Morphism.thm phi Sb_comp_right,
  map_Sb_strong = Morphism.thm phi map_Sb_strong
}: mrsbnf_facts

datatype mrsbnf = MRSBNF of {
  mrbnfs: MRBNF_Def.mrbnf list,
  pbmv_monad: BMV_Monad_Def.bmv_monad,
  axioms: thm mrsbnf_axioms list,
  facts: mrsbnf_facts list
}

fun morph_mrsbnf phi (MRSBNF {
    mrbnfs, pbmv_monad, axioms, facts
}) = MRSBNF {
  mrbnfs = map (MRBNF_Def.morph_mrbnf phi) mrbnfs,
  pbmv_monad = BMV_Monad_Def.morph_bmv_monad phi pbmv_monad,
  axioms = map (morph_mrsbnf_axioms phi) axioms,
  facts = map (morph_mrsbnf_facts phi) facts
}

val id_bmv_monad = the (BMV_Monad_Def.pbmv_monad_of @{context} "BMV_Monad.ID");

fun mk_id_bmv_monad free = BMV_Monad_Def.morph_bmv_monad (
  MRBNF_Util.subst_typ_morphism [(hd (hd (BMV_Monad_Def.frees_of_bmv_monad id_bmv_monad)), TFree free)]
) id_bmv_monad;

fun Rep_mrsbnf (MRSBNF x) = x

val bmv_monad_of_mrsbnf = #pbmv_monad o Rep_mrsbnf
val mrbnfs_of_mrsbnf = #mrbnfs o Rep_mrsbnf
val axioms_of_mrsbnf = #axioms o Rep_mrsbnf
val facts_of_mrsbnf = #facts o Rep_mrsbnf

structure Data = Generic_Data (
  type T = mrsbnf Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
);

fun register_mrsbnf name bmv =
  Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
    (fn phi => Data.map (Symtab.update (name, morph_mrsbnf phi bmv)));

fun mrsbnf_of_generic context =
  Option.map (morph_mrsbnf (Morphism.transfer_morphism (Context.theory_of context)))
  o Symtab.lookup (Data.get context);

val mrsbnf_of = mrsbnf_of_generic o Context.Proof;

fun note_mrsbnf_thms fact_policy qualify name_opt mrsbnf lthy =
  let
    val bmv = bmv_monad_of_mrsbnf mrsbnf;
    val name = case name_opt of
      NONE => fst (dest_Type (nth (BMV_Monad_Def.ops_of_bmv_monad bmv) (BMV_Monad_Def.leader_of_bmv_monad bmv)))
      | SOME b => b;
    val axioms = axioms_of_mrsbnf mrsbnf;
    val facts = facts_of_mrsbnf mrsbnf;

    fun note_unless_dont_note (noted, lthy) =
      let val notes =
        [("map_is_Sb", map #map_is_Sb axioms, []),
         ("set_Vrs", maps #set_Vrs axioms, []),
         ("set_Sb", maps #set_Sb axioms, []),
         ("map_Sb'", maps (the_default [] o Option.map single o #map_Sb) axioms, []),
         ("SSupp_map_subset", maps (map_filter I o #SSupp_map_subset) facts, []),
         ("SSupp_map_bound", maps (map_filter I o #SSupp_map_bound) facts, []),
         ("map_Inj", maps (map_filter I o #map_Inj) facts, []),
         ("Sb_comp_right", map #Sb_comp_right facts, []),
         ("map_Sb_strong", map #map_Sb_strong facts, [])
        ]
        |> filter_out (null o #2)
        |> map (fn (thmN, thms, attrs) => ((qualify (Binding.qualify true (short_type_name name) (Binding.name thmN)), attrs), [(thms, [])]));
      in Local_Theory.notes notes lthy |>> append noted end
    val fact_policy = fact_policy (Proof_Context.theory_of lthy);
  in ([], lthy)
    |> fact_policy <> BNF_Def.Dont_Note ? note_unless_dont_note
  end

fun mk_mrsbnf fact_policy qualify (deads, As, As', Bs, Fs, fs) name_opt mrbnfs bmv axioms' lthy =
  let
    val names = map (fst o dest_Free);
    val facts' = @{map 7} (fn axioms => fn mrbnf => fn bmv_axioms => fn bmv_facts => fn Sb => fn Injs => fn SSupps =>
      let
        val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
        val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;

        val T = body_type (fastype_of Sb);
        val fs = map (fn T => the (List.find (curry (op=) T o fastype_of) fs)) (fst (split_last (binder_types (fastype_of mapx))));

        val f_prems = map HOLogic.mk_Trueprop (flat (map2 (fn f => fn MRBNF_Def.Live_Var => []
          | MRBNF_Def.Bound_Var => [mk_bij f, mk_supp_bound f]
          | MRBNF_Def.Free_Var => [mk_supp_bound f]
        ) fs var_types));
        val (live_fs, bound_fs, free_fs) = MRBNF_Def.deinterlace fs var_types;

        val (((gs, aa), x), _) = lthy
          |> mk_Frees "g" (map fastype_of Injs)
          ||>> mk_Frees "a" (map (domain_type o fastype_of) Injs)
          ||>> apfst hd o mk_Frees "x" [T];
        val frees = inter (op=) Fs (MRBNF_Def.frees_of_mrbnf mrbnf);
        val free = length frees;

        val live = MRBNF_Def.live_of_mrbnf mrbnf;

        val g_prems = map2 (fn (SSupp, _) => fn g => HOLogic.mk_Trueprop (
          mk_ordLess (mk_card_of (SSupp $ g)) (mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of g))))
        )) SSupps gs;
        fun find_f T = List.find (fn f => T = domain_type (fastype_of f)) fs;

        val Sb_comp_right =
          let
            val fs' = map (the o find_f o domain_type o fastype_of) gs;
            val f'_prems = map (HOLogic.mk_Trueprop o mk_supp_bound) fs';
            val goal = Term.subst_atomic_types (As' ~~ As) (mk_Trueprop_eq (
              Term.list_comb (Sb, map2 (curry HOLogic.mk_comp) gs fs'),
              HOLogic.mk_comp (
                Term.list_comb (Sb, gs),
                Term.list_comb (mapx, map (fn T => case List.find (fn f => (domain_type T) = domain_type (fastype_of f)) fs' of
                  SOME f => f | NONE => HOLogic.id_const (domain_type T)
                ) (fst (split_last (binder_types (fastype_of mapx)))))
              )
            ));
          in Goal.prove_sorry lthy (names (fs' @ gs)) (f'_prems @ g_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            EqSubst.eqsubst_tac ctxt [0] [#map_is_Sb axioms],
            REPEAT_DETERM o resolve_tac ctxt prems,
            rtac ctxt sym,
            rtac ctxt trans,
            rtac ctxt (#Sb_comp bmv_axioms),
            REPEAT_DETERM o resolve_tac ctxt (prems @ #SSupp_comp_bound bmv_facts @ #SSupp_Inj_bound bmv_facts),
            K (Local_Defs.unfold0_tac ctxt @{thms comp_assoc[symmetric]}),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (maps #Sb_comp_Injs (BMV_Monad_Def.axioms_of_bmv_monad bmv)),
              REPEAT_DETERM o resolve_tac ctxt prems
            ],
            rtac ctxt refl
          ]) end;

        val map_Inj = @{map 3} (fn Inj => fn f => fn a => if body_type (fastype_of Inj) <> T then NONE else
          let val goal = mk_Trueprop_eq (Term.list_comb (mapx, fs) $ (Inj $ a), Inj $ (f $ a))
          in SOME (Goal.prove_sorry lthy (names (fs @ [a])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt trans,
            rtac ctxt (#map_is_Sb axioms RS fun_cong),
            REPEAT_DETERM o resolve_tac ctxt prems,
            rtac ctxt trans,
            resolve_tac ctxt (map (fn thm => @{thm trans[OF comp_apply[symmetric]]} OF [thm RS fun_cong]) (#Sb_comp_Injs bmv_axioms)),
            REPEAT_DETERM o resolve_tac ctxt (prems @ #SSupp_comp_bound bmv_facts @ #SSupp_Inj_bound bmv_facts),
            rtac ctxt @{thm comp_apply}
          ])) end
        ) Injs free_fs aa;

        val SSupp_map_subset = @{map 3} (fn (SSupp, SSupp_def) => fn g => fn g_prem =>
          let
            val map_t = Term.list_comb (mapx, fs);
            val SSupp' = Term.subst_atomic_types (As' ~~ As') SSupp;
            val goal = HOLogic.mk_Trueprop (uncurry mk_leq (
              SSupp' $ HOLogic.mk_comp (map_t, g),
              mk_Un (SSupp $ g, mk_supp (the (find_f (HOLogic.dest_setT (body_type (fastype_of SSupp))))))
            ));
          in if body_type (fastype_of map_t) <> body_type (domain_type (fastype_of SSupp')) then NONE else
            SOME (Goal.prove_sorry lthy (names (g :: fs)) (f_prems @ [g_prem]) goal (fn {context=ctxt, prems} => EVERY1 [
              rtac ctxt @{thm subsetI},
              EqSubst.eqsubst_tac ctxt [0] [SSupp_def],
              EqSubst.eqsubst_asm_tac ctxt [0] [SSupp_def],
              K (Local_Defs.unfold0_tac ctxt @{thms mem_Collect_eq Un_iff comp_def}),
              rtac ctxt @{thm case_split[rotated]},
              etac ctxt disjI1,
              rtac ctxt disjI2,
              dtac ctxt @{thm iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated]},
              rtac ctxt (mk_arg_cong lthy 1 map_t),
              assume_tac ctxt,
              EqSubst.eqsubst_asm_tac ctxt [0] (map_filter I map_Inj),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
              rotate_tac ~1,
              etac ctxt @{thm contrapos_np},
              K (Local_Defs.unfold0_tac ctxt (#Inj_inj bmv_facts)),
              etac ctxt @{thm notin_supp}
            ]))
          end
        ) SSupps gs g_prems;

        val Un_bound = MRBNF_Def.get_class_assumption [BMV_Monad_Def.var_class_of_bmv_monad bmv] "Un_bound" lthy;

        val SSupp_map_bound = @{map 4} (fn (SSupp, _) => fn g => fn g_prem => Option.map (fn thm =>
          let val goal = HOLogic.mk_Trueprop (uncurry mk_ordLess (
            mk_card_of (SSupp $ HOLogic.mk_comp (Term.list_comb (mapx, fs), g)),
            mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of g)))
          ));
          in Goal.prove_sorry lthy (names (fs @ [g])) (f_prems @ [g_prem]) goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt @{thm card_of_subset_bound},
            rtac ctxt thm,
            REPEAT_DETERM o resolve_tac ctxt prems,
            rtac ctxt Un_bound,
            REPEAT_DETERM o resolve_tac ctxt prems
          ]) end
        )) SSupps gs g_prems SSupp_map_subset;
        in {
          SSupp_map_subset = SSupp_map_subset,
          SSupp_map_bound = SSupp_map_bound,
          map_Inj = map_Inj,
          Sb_comp_right = Sb_comp_right
        } end
    ) axioms' mrbnfs (BMV_Monad_Def.axioms_of_bmv_monad bmv) (BMV_Monad_Def.facts_of_bmv_monad bmv)
      (BMV_Monad_Def.Sbs_of_bmv_monad bmv) (BMV_Monad_Def.Injs_of_bmv_monad bmv)
      (BMV_Monad_Def.SSupps_of_bmv_monad bmv);

    val facts' = @{map 8} (fn axioms => fn facts => fn mrbnf => fn bmv_axioms => fn bmv_facts => fn Sb => fn Injs => fn SSupps =>
      let
        val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
        val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
        val live = MRBNF_Def.live_of_mrbnf mrbnf;

        val T = body_type (fastype_of Sb);
        val fs = map (fn T => the (List.find (curry (op=) T o fastype_of) fs)) (fst (split_last (binder_types (fastype_of mapx))));
        val (live_fs, bound_fs, free_fs) = MRBNF_Def.deinterlace fs var_types;

        val (((gs, aa), x), _) = lthy
          |> mk_Frees "g" (map fastype_of Injs)
          ||>> mk_Frees "a" (map (domain_type o fastype_of) Injs)
          ||>> apfst hd o mk_Frees "x" [T];
        val frees = inter (op=) Fs (MRBNF_Def.frees_of_mrbnf mrbnf);
        val free = length frees;

        val g_prems = map2 (fn (SSupp, _) => fn g => HOLogic.mk_Trueprop (
          mk_ordLess (mk_card_of (SSupp $ g)) (mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of g))))
        )) SSupps gs;

        val map_Sb_strong =
          let
            val map_t = Term.list_comb (mapx, fs);
            val mrbnfs = map (fn Inj =>
              the (List.find (fn mrbnf => body_type (fastype_of (MRBNF_Def.map_of_mrbnf mrbnf)) = body_type (fastype_of Inj)) mrbnfs)
            ) Injs;
            fun find_f T = List.find (curry (op=) T o domain_type o fastype_of) fs;
            val goal = mk_Trueprop_eq (
              HOLogic.mk_comp (map_t, Term.list_comb (Sb, gs)),
              HOLogic.mk_comp (Term.list_comb (Term.subst_atomic_types (As ~~ As') Sb, map2 (fn g => fn mrbnf =>
                let val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
                in HOLogic.mk_comp (HOLogic.mk_comp (
                  Term.list_comb (mapx,
                    map (the o find_f o domain_type) (fst (split_last (binder_types (fastype_of mapx))))
                  ),
                  g), mk_inv (the (find_f (domain_type (fastype_of g))))
                ) end
              ) gs mrbnfs), map_t)
            );

            val f_prems = flat (MRBNF_Def.interlace (replicate live [])
              (map (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) bound_fs)
              (map (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) free_fs) var_types);
            val id_of_f = HOLogic.id_const o domain_type o fastype_of
            val count = live + MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.free_of_mrbnf mrbnf - length frees;
          in Goal.prove_sorry lthy (names (fs @ gs)) (f_prems @ g_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            if count = 0 then K all_tac else EVERY' [
              rtac ctxt trans,
              rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
              rtac ctxt trans,
              K (prefer_tac 2),
              rtac ctxt (infer_instantiate' ctxt (
                map (SOME o Thm.cterm_of ctxt) (flat (
                  MRBNF_Def.interlace (replicate (2 * live) [])
                    (map single bound_fs @ map (single o id_of_f) bound_fs)
                    (map (single o id_of_f) free_fs @ map single free_fs) (var_types @ var_types)
                ) @ maps (fn f => [HOLogic.id_const (body_type (fastype_of f)), f]) live_fs)
              ) (MRBNF_Def.map_comp0_of_mrbnf mrbnf)),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
              rtac ctxt refl,
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc}),
              EqSubst.eqsubst_tac ctxt [0] [the (#map_Sb axioms)],
              REPEAT_DETERM o resolve_tac ctxt prems,
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc[symmetric]}),
              rtac ctxt trans,
              rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]}
            ],
            EqSubst.eqsubst_tac ctxt [0] [#map_is_Sb axioms],
            REPEAT_DETERM o resolve_tac ctxt prems,
            rtac ctxt trans,
            rtac ctxt (#Sb_comp bmv_axioms),
            REPEAT_DETERM o resolve_tac ctxt (prems @ #SSupp_comp_bound bmv_facts @ #SSupp_Inj_bound bmv_facts),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (map (fn ax => #map_is_Sb ax RS sym) axioms'),
              REPEAT_DETERM o resolve_tac ctxt prems
            ],
            if count = 0 then K all_tac else rtac ctxt refl,
            rtac ctxt sym,
            rtac ctxt trans,
            rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
            rtac ctxt (#Sb_comp_right facts),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound}
              @ maps (map_filter I o #SSupp_map_bound) facts' @ prems @ #SSupp_comp_bound bmv_facts
            ),
            K (Local_Defs.unfold0_tac ctxt @{thms comp_assoc}),
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym],
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_inv_bound bij_imp_bij_inv} @ prems),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
              resolve_tac ctxt prems
            ],
            K (Local_Defs.unfold0_tac ctxt (MRBNF_Def.map_id0_of_mrbnf mrbnf :: @{thms id_o o_id})),
            rtac ctxt refl
          ]) end;
      in {
        SSupp_map_subset = #SSupp_map_subset facts,
        SSupp_map_bound = #SSupp_map_bound facts,
        map_Inj = #map_Inj facts,
        Sb_comp_right = #Sb_comp_right facts,
        map_Sb_strong = map_Sb_strong
      }: mrsbnf_facts end
    ) axioms' facts' mrbnfs (BMV_Monad_Def.axioms_of_bmv_monad bmv) (BMV_Monad_Def.facts_of_bmv_monad bmv)
      (BMV_Monad_Def.Sbs_of_bmv_monad bmv) (BMV_Monad_Def.Injs_of_bmv_monad bmv)
      (BMV_Monad_Def.SSupps_of_bmv_monad bmv);

    val mrsbnf = MRSBNF {
      mrbnfs = mrbnfs,
      pbmv_monad = bmv,
      axioms = axioms',
      facts = facts'
    };

    val (_, lthy) = note_mrsbnf_thms fact_policy qualify name_opt mrsbnf lthy;
  in (mrsbnf, lthy) end;

fun mk_mrsbnf_axioms mrbnfs bmv lthy =
  let
    val leader = BMV_Monad_Def.leader_of_bmv_monad bmv;
    val lmrbnf = nth mrbnfs leader;
    val (((((Fs, Bs), As), As'), deads), names_lthy) = lthy
      |> mk_TFrees' (map Type.sort_of_atyp (MRBNF_Def.frees_of_mrbnf lmrbnf))
      ||>> mk_TFrees' (map Type.sort_of_atyp (MRBNF_Def.bounds_of_mrbnf lmrbnf))
      ||>> mk_TFrees (MRBNF_Def.live_of_mrbnf lmrbnf)
      ||>> mk_TFrees (MRBNF_Def.live_of_mrbnf lmrbnf)
      ||>> mk_TFrees' (map Type.sort_of_atyp (MRBNF_Def.deads_of_mrbnf lmrbnf));

    val (fs, names_lthy) = names_lthy
      |> mk_Frees "f" (MRBNF_Def.interlace (map2 (curry (op-->)) As As') (map (fn a => a --> a) Bs) (map (fn a => a --> a) Fs) (MRBNF_Def.var_types_of_mrbnf lmrbnf));

    local
      val (mapx, Sb) = case nth (BMV_Monad_Def.Maps_of_bmv_monad bmv) leader of
        NONE => (MRBNF_Def.mk_map_of_mrbnf deads As As Bs Fs lmrbnf, nth (BMV_Monad_Def.Sbs_of_bmv_monad bmv) leader)
        | SOME Map => (MRBNF_Def.mk_map_of_mrbnf deads As As' Bs Fs lmrbnf, Map)

      val tyenv = fold (Sign.typ_match (Proof_Context.theory_of lthy)
      ) [apply2 (snd o split_last o binder_types o fastype_of) (Sb, mapx), apply2 (body_type o fastype_of) (Sb, mapx)] Vartab.empty;

      val phi = Morphism.morphism "subst types" {
        binding = [], fact = [],
        typ = [K (Envir.subst_type tyenv)],
        term = [K (Envir.subst_term (tyenv, Vartab.empty))]
      }
    in
      val bmv = BMV_Monad_Def.morph_bmv_monad phi bmv;

      val mrbnfs = @{map 3} (fn mrbnf => fn Sb => fn Map =>
        let
          val Sb = the_default Sb Map;
          val mapx = MRBNF_Def.map_of_mrbnf mrbnf;

          val tyenv = fold (Sign.typ_match (Proof_Context.theory_of lthy)
          ) [apply2 (snd o split_last o binder_types o fastype_of) (mapx, Sb), apply2 (body_type o fastype_of) (mapx, Sb)] Vartab.empty;

          val phi = Morphism.morphism "subst types" {
            binding = [], fact = [],
            typ = [K (Envir.subst_type tyenv)],
            term = [K (Envir.subst_term (tyenv, Vartab.empty))]
          };
        in MRBNF_Def.morph_mrbnf phi mrbnf end
      ) mrbnfs (BMV_Monad_Def.Sbs_of_bmv_monad bmv) (BMV_Monad_Def.Maps_of_bmv_monad bmv);
    end;

    val axioms = @{map 6} (fn mrbnf => fn Sb => fn Injs => fn SSupps => fn Vrs => fn bmv_frees =>
      let
        val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
        val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;

        val fs = map (fn T => the (List.find (curry (op=) T o fastype_of) fs)) (fst (split_last (binder_types (fastype_of mapx))));

        val (live_fs, bound_fs, free_fs') = MRBNF_Def.deinterlace fs var_types;

        val frees = inter (op=) (take (length (BMV_Monad_Def.frees_of_bmv_monad bmv)) Fs) (MRBNF_Def.frees_of_mrbnf mrbnf);
        val pfrees = subtract (op=) frees (MRBNF_Def.frees_of_mrbnf mrbnf);

        val free = length frees;
        val free_fs = take free free_fs';
        val free_prems = map (fn f => HOLogic.mk_Trueprop (mk_supp_bound f)) free_fs;

        val map_is_Sb = fold_rev Logic.all free_fs (fold_rev (curry Logic.mk_implies) free_prems (mk_Trueprop_eq (
          Term.list_comb (Term.subst_atomic_types (As' ~~ As) mapx, MRBNF_Def.interlace
            (map HOLogic.id_const As) (map HOLogic.id_const Bs) (free_fs @ map HOLogic.id_const (drop (length frees) Fs))
            (MRBNF_Def.var_types_of_mrbnf mrbnf)
          ),
          Term.list_comb (Sb, map (fn Inj =>
            HOLogic.mk_comp (Inj, the (List.find (fn f => (op=) (apply2 (domain_type o fastype_of) (Inj, f))) fs))
          ) Injs)
        )));

        val ((gs, x), _) = names_lthy
          |> mk_Frees "g" (map fastype_of Injs)
          ||>> apfst hd o mk_Frees "x" [body_type (fastype_of Sb)];

        val live = MRBNF_Def.live_of_mrbnf mrbnf;
        val pfree_fs = drop free free_fs';
        val other_prems = flat (MRBNF_Def.interlace (replicate live [])
          (map (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) bound_fs)
          (replicate free [] @ map (fn f => [HOLogic.mk_Trueprop (mk_supp_bound f)]) pfree_fs)
          var_types
        );
        val other_fs = flat (MRBNF_Def.interlace (map single live_fs) (map single bound_fs)
          (replicate free [] @ map single pfree_fs) var_types);

        val g_prems = map2 (fn (SSupp, _) => fn g => HOLogic.mk_Trueprop (uncurry mk_ordLess (
          mk_card_of (SSupp $ g), mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of g)))
        ))) SSupps gs;

        val count = live + MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf;
        val map_Sb = if count - free = 0 then NONE else
          let
            val map_t = Term.list_comb (mapx, MRBNF_Def.interlace live_fs bound_fs (map HOLogic.id_const frees @ pfree_fs) var_types);
            val Sb_t = Term.list_comb (Sb, gs);
          in SOME (fold_rev Logic.all (other_fs @ gs) (fold_rev (curry Logic.mk_implies) (other_prems @ g_prems) (mk_Trueprop_eq (
            HOLogic.mk_comp (map_t, Sb_t),
            HOLogic.mk_comp (Term.subst_atomic_types (As ~~ As') Sb_t, map_t)
          )))) end;

        val sets = MRBNF_Def.sets_of_mrbnf mrbnf;
        val (live_sets, bound_sets, free_sets) = MRBNF_Def.deinterlace sets var_types;

        val set_Sbs =
          let
            val sets' = flat (MRBNF_Def.interlace (map single live_sets) (map single bound_sets)
              (replicate free [] @ map single (drop free free_sets)) var_types);
          in map (fn set => fold_rev Logic.all (gs @ [x]) (fold_rev (curry Logic.mk_implies) g_prems (
            mk_Trueprop_eq (set $ (Term.list_comb (Sb, gs) $ x), set $ x)
          ))) sets' end;

        val Vrs' = bmv_frees ~~ transpose Vrs;
        val set_Vrs = map (fn set =>
          let
            val aT = HOLogic.dest_setT (fastype_of (set $ x));
            val Vrs = the (AList.lookup (op=) Vrs' aT);
            val Vrs' = map_filter (Option.map (fn Vrs => Vrs $ x)) Vrs;
          in Logic.all x (mk_Trueprop_eq (set $ x, case Vrs' of
            [] => mk_bot aT
            | _ => foldl1 mk_Un Vrs'
          )) end
        ) (take free free_sets);
      in {
        map_is_Sb = map_is_Sb,
        set_Vrs = set_Vrs,
        map_Sb = map_Sb,
        set_Sb = set_Sbs
      }: term mrsbnf_axioms end
    ) mrbnfs (BMV_Monad_Def.Sbs_of_bmv_monad bmv) (BMV_Monad_Def.Injs_of_bmv_monad bmv)
      (BMV_Monad_Def.SSupps_of_bmv_monad bmv) (BMV_Monad_Def.Vrs_of_bmv_monad bmv)
      (BMV_Monad_Def.frees_of_bmv_monad bmv);

  in (axioms, (deads, As, As', Bs, Fs, fs), mrbnfs, bmv) end

fun prove_axioms mrbnfs bmv tacs lthy =
  let
    val (goals, vars, mrbnfs, bmv) = mk_mrsbnf_axioms mrbnfs bmv lthy;
    val tacs' = map (map_mrsbnf_axioms (fn tac => fn goal => Goal.prove_sorry lthy [] [] goal (tac o #context))) tacs;
  in (map2 apply_mrsbnf_axioms tacs' goals, vars, mrbnfs, bmv) end

fun mrsbnf_def fact_policy qualify name_opt mrbnfs bmv tacs lthy =
  let
    val (axioms, vars, mrbnfs, bmv) = prove_axioms mrbnfs bmv tacs lthy;
  in mk_mrsbnf fact_policy qualify vars name_opt mrbnfs bmv axioms lthy end

fun pbmv_monad_of_typ _ _ _ xs _ (TFree x) accum = if member (op=) xs x
    then (NONE, accum) else (SOME (mk_id_bmv_monad x), accum)
  | pbmv_monad_of_typ _ _ _ _ _ (TVar _) _ = error "unexpected schematic variable"
  | pbmv_monad_of_typ optim const_policy inline_policy xs qualify' (T as Type (n, Ts)) (accum, lthy) =
    let val (bmv_opt, lthy) = case BMV_Monad_Def.pbmv_monad_of lthy n of
      SOME bmv => (SOME bmv, lthy)
      | NONE => case BNF_Def.bnf_of lthy n of
        SOME bnf =>
          let val (bmv, lthy) = BMV_Monad_Def.pbmv_monad_of_bnf bnf lthy
          in (SOME bmv, BMV_Monad_Def.register_pbmv_monad n bmv lthy) end
        | NONE => (NONE, lthy);
    in case bmv_opt of
      NONE => (NONE, (accum, lthy))
      | SOME bmv => if null (nth (BMV_Monad_Def.lives_of_bmv_monad bmv) (BMV_Monad_Def.leader_of_bmv_monad bmv)) then
          let val T = nth (BMV_Monad_Def.ops_of_bmv_monad bmv) (BMV_Monad_Def.leader_of_bmv_monad bmv)
          in (SOME (BMV_Monad_Def.morph_bmv_monad (MRBNF_Util.subst_typ_morphism (
            rev (map TFree (Term.add_tfreesT T []) @ map TVar (Term.add_tvarsT T [])) ~~ Ts
          )) bmv), (accum, lthy)) end
        else let
          val name = Long_Name.base_name n;

          fun qualify i =
              let val namei = name ^ nonzero_string_of_int i;
              in qualify' o Binding.qualify true namei end;

          val leader = BMV_Monad_Def.leader_of_bmv_monad bmv;
          val T = nth (BMV_Monad_Def.ops_of_bmv_monad bmv) leader;
          val bmv = BMV_Monad_Def.morph_bmv_monad (
            MRBNF_Util.subst_typ_morphism (snd (dest_Type T) ~~ Ts)
          ) bmv;
          val bmv = BMV_Monad_Def.morph_bmv_monad (MRBNF_Util.subst_typ_morphism (
             nth (BMV_Monad_Def.lives'_of_bmv_monad bmv) leader ~~ nth (BMV_Monad_Def.lives_of_bmv_monad bmv) leader
          )) bmv;
          val live_Ts = nth (BMV_Monad_Def.lives_of_bmv_monad bmv) leader;

          val qualifies = map qualify (1 upto length live_Ts);
          val (bmv_opts, (accum, lthy)) = @{fold_map 2} (pbmv_monad_of_typ optim const_policy inline_policy xs) qualifies live_Ts (accum, lthy)
          val bmvs = map2 (fn T => fn NONE => Inr T | SOME bmv => Inl bmv) live_Ts bmv_opts;
        in if exists Option.isSome bmv_opts then
          let val ((bmv, unfold_set), lthy) = BMV_Monad_Def.compose_bmv_monad (qualify 0) bmv bmvs lthy;
          in (SOME bmv, (unfold_set @ accum, lthy)) end
        else
          (NONE, (accum, lthy))
        end
    end;

fun mrsbnf_cmd (b, Ts) lthy =
  let
    val Ts = map (Syntax.read_typ lthy) Ts;
    val name = if Binding.is_empty b then fst (dest_Type (hd Ts)) else Local_Theory.full_name lthy b;
    val (mrbnfs, lthy) = fold_map (fn T => fn lthy => case T of
      TFree _ => (BMV_Monad_Def.id_mrbnf, lthy)
      | TVar _ => error "Illegal schematic variable"
      | Type (name, _) => case MRBNF_Def.mrbnf_of lthy name of
        SOME mrbnf => (mrbnf, lthy)
        | NONE => case BNF_Def.bnf_of lthy name of
          SOME bnf => MRBNF_Def.mrbnf_of_bnf bnf lthy
          | NONE => error ("Type " ^ name ^ " is not a (MR)BNF")
    ) Ts lthy;
    val bmv_monad = case BMV_Monad_Def.pbmv_monad_of lthy name of
      SOME bmv => bmv
      | NONE => error ("Type " ^ name ^ " is not a PBMV Monad")

    val (goals, vars, mrbnfs, bmv) = mk_mrsbnf_axioms mrbnfs bmv_monad lthy;

    fun after_qed thmss lthy =
      let
        val thms = map hd thmss;

        fun chop_opt NONE thms = (NONE, thms)
          | chop_opt (SOME _) thms = (SOME (hd thms), tl thms)

        val axioms = fst (fold_map (fn goals => fn thms =>
          let val ((((map_is_Sb, set_Vrs), map_Sb), set_Sb), thms) = thms
            |> apfst hd o chop 1
            ||>> chop (length (#set_Vrs goals))
            ||>> chop_opt (#map_Sb goals)
            ||>> chop (length (#set_Sb goals));
          in ({
            map_is_Sb = map_is_Sb,
            set_Vrs = set_Vrs,
            map_Sb = map_Sb,
            set_Sb = set_Sb
          }: thm mrsbnf_axioms, thms) end
        ) goals thms);

        val (mrsbnf, lthy) = mk_mrsbnf (K BNF_Def.Note_Some) I vars (SOME name) mrbnfs bmv axioms lthy;
        val lthy = register_mrsbnf name mrsbnf lthy;
      in lthy end

  in Proof.theorem NONE after_qed (map (single o rpair []) (maps (fn goals =>
    #map_is_Sb goals :: #set_Vrs goals @ the_default [] (Option.map single (#map_Sb goals)) @ #set_Sb goals
  ) goals)) lthy
    |> Proof.refine_singleton (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (TRYALL (rtac ctxt refl))))
  end

val _ = Outer_Syntax.local_theory_to_proof @{command_keyword mrsbnf}
  "register a map-restricted substitutive bounded natural functor"
  ((parse_opt_binding_colon -- Parse.and_list1 Parse.typ) >> mrsbnf_cmd)

end