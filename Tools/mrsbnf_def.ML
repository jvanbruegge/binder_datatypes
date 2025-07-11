signature MRSBNF_DEF = sig
  type mrsbnf

  type 'a mrsbnf_axioms = {
    map_is_Sb: 'a,
    set_Vrs: 'a list,
    map_Sb: 'a option,
    map_Injs: 'a list option,
    set_Sb: 'a list
  };

  type mrsbnf_facts = {
    SSupp_map_subset: thm option list,
    SSupp_map_bound: thm option list,
    map_Inj: thm option list,
    map_Sb_strong: thm,
    Map_map: thm option,
    set_Injs: thm list list
  };

  val bmv_monad_of_mrsbnf: mrsbnf -> BMV_Monad_Def.bmv_monad
  val mrbnfs_of_mrsbnf: mrsbnf -> MRBNF_Def.mrbnf list
  val axioms_of_mrsbnf: mrsbnf -> thm mrsbnf_axioms list
  val facts_of_mrsbnf: mrsbnf -> mrsbnf_facts list

  val morph_mrsbnf: morphism -> mrsbnf -> mrsbnf

  val mrsbnf_def: (theory -> BNF_Def.fact_policy) -> (binding -> binding) -> string option
    -> MRBNF_Def.mrbnf list -> BMV_Monad_Def.bmv_monad -> (Proof.context -> tactic) mrsbnf_axioms list
    -> local_theory -> mrsbnf * local_theory;

  val mrsbnf_of_mrbnf: MRBNF_Def.mrbnf -> local_theory -> mrsbnf * local_theory;

  val note_mrsbnf_thms: (theory -> BNF_Def.fact_policy) -> (binding -> binding) -> string option -> mrsbnf
    -> local_theory -> (string * thm list) list * local_theory
  val register_mrsbnf: string -> mrsbnf -> local_theory -> local_theory;
  val mrsbnf_of_generic: Context.generic -> string -> mrsbnf option;
  val mrsbnf_of: Proof.context -> string -> mrsbnf option;
end

structure MRSBNF_Def : MRSBNF_DEF = struct

open MRBNF_Util
open BMV_Monad_Def

type 'a mrsbnf_axioms = {
  map_is_Sb: 'a,
  set_Vrs: 'a list,
  map_Sb: 'a option,
  map_Injs: 'a list option,
  set_Sb: 'a list
}

fun map_mrsbnf_axioms (f:'a -> 'b) ({ map_is_Sb, set_Vrs, map_Sb, set_Sb, map_Injs }: 'a mrsbnf_axioms) = {
  map_is_Sb = f map_is_Sb,
  set_Vrs = map f set_Vrs,
  map_Sb = Option.map f map_Sb,
  map_Injs = Option.map (map f) map_Injs,
  set_Sb = map f set_Sb
}: 'b mrsbnf_axioms;

val morph_mrsbnf_axioms = map_mrsbnf_axioms o Morphism.thm

fun apply_mrsbnf_axioms ({
  map_is_Sb=f1, map_Sb=f2, set_Sb=f3s, set_Vrs=f4s, map_Injs=f5s
}: ('a -> 'b) mrsbnf_axioms) ({
  map_is_Sb, map_Sb, set_Sb, set_Vrs, map_Injs
}: 'a mrsbnf_axioms) =
let
  fun checkLength name xs ys = if length xs <> length ys then error (
    "UnequalLength: " ^ name ^ " (" ^ string_of_int (length xs) ^ " vs. " ^ string_of_int (length ys) ^ ")"
  ) else ()
  val _ = checkLength "set_Sb" set_Sb f3s
  val _ = checkLength "set_Vrs" set_Vrs f4s
  val _ = Option.map (fn map_Injs => checkLength "map_Injs" map_Injs (the f5s)) map_Injs
in {
  map_is_Sb = f1 map_is_Sb,
  map_Sb = Option.map (fn t => the f2 t) map_Sb,
  map_Injs = Option.map (fn ts => map2 (curry (op|>)) ts (the f5s)) map_Injs,
  set_Sb = map2 (curry (op|>)) set_Sb f3s,
  set_Vrs = map2 (curry (op|>)) set_Vrs f4s
}: 'b mrsbnf_axioms end

type mrsbnf_facts = {
  SSupp_map_subset: thm option list,
  SSupp_map_bound: thm option list,
  map_Inj: thm option list,
  map_Sb_strong: thm,
  Map_map: thm option,
  set_Injs: thm list list
}

fun morph_mrsbnf_facts phi ({
    SSupp_map_subset, SSupp_map_bound, map_Inj, map_Sb_strong, Map_map, set_Injs
}: mrsbnf_facts) = {
  SSupp_map_subset = map (Option.map (Morphism.thm phi)) SSupp_map_subset,
  SSupp_map_bound = map (Option.map (Morphism.thm phi)) SSupp_map_bound,
  map_Inj = map (Option.map (Morphism.thm phi)) map_Inj,
  map_Sb_strong = Morphism.thm phi map_Sb_strong,
  Map_map = Option.map (Morphism.thm phi) Map_map,
  set_Injs = map (map (Morphism.thm phi)) set_Injs
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

fun register_mrsbnf name mrsbnf =
  Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
    (fn phi => Data.map (Symtab.update (name, morph_mrsbnf phi mrsbnf)));

fun mrsbnf_of_generic context =
  Option.map (morph_mrsbnf (Morphism.transfer_morphism (Context.theory_of context)))
  o Symtab.lookup (Data.get context);

val mrsbnf_of = mrsbnf_of_generic o Context.Proof;

fun note_mrsbnf_thms fact_policy qualify name_opt mrsbnf lthy =
  let
    val bmv = bmv_monad_of_mrsbnf mrsbnf;
    fun name () = case name_opt of
      NONE => fst (dest_Type (nth (BMV_Monad_Def.ops_of_bmv_monad bmv) (BMV_Monad_Def.leader_of_bmv_monad bmv)))
      | SOME b => b;
    val axioms = axioms_of_mrsbnf mrsbnf;
    val facts = facts_of_mrsbnf mrsbnf;
    val unfolds = BMV_Monad_Def.unfolds_of_bmv_monad bmv;

    fun note_unless_dont_note (noted, lthy) =
      let val notes =
        [("map_is_Sb", map #map_is_Sb axioms, []),
         ("set_Vrs", maps #set_Vrs axioms, []),
         ("set_Sb", maps #set_Sb axioms, []),
         ("map_Sb", maps (the_default [] o Option.map single o #map_Sb) axioms, []),
         ("SSupp_map_subset", maps (map_filter I o #SSupp_map_subset) facts, []),
         ("SSupp_map_bound", maps (map_filter I o #SSupp_map_bound) facts, []),
         ("map_Inj_raw", maps (the_default [] o #map_Injs) axioms, []),
         ("map_Inj", maps (map_filter I o #map_Inj) facts, []),
         ("map_Sb_strong", map #map_Sb_strong facts, []),
         ("Map_map", map_filter #Map_map facts, []),
         ("set_Inj", flat (maps #set_Injs facts), [])
        ]
        |> filter_out (null o #2)
        |> map (fn (thmN, thms, attrs) => ((qualify (Binding.qualify true (short_type_name (name ())) (Binding.name thmN)), attrs), [
          (map (Local_Defs.unfold0 lthy unfolds) thms, [])
        ]));
      in Local_Theory.notes notes lthy |>> append noted end
    val fact_policy = fact_policy (Proof_Context.theory_of lthy);
  in ([], lthy)
    |> fact_policy <> BNF_Def.Dont_Note ? note_unless_dont_note
  end

fun mk_mrsbnf fact_policy qualify (deads, As, As', Bs, Fs, fs) name_opt mrbnfs bmv axioms' lthy =
  let
    val no_reflexive = filter_out (fn thm => case try (HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm of
      NONE => false
      | SOME (rhs, lhs) => rhs = lhs
    );

    val names = map (fst o dest_Free);
    val facts' = @{map 12} (fn lives => fn lives' => fn axioms => fn mrbnf => fn bmv_axioms => fn bmv_params => fn bmv_facts => fn Sb => fn Injs => fn RVrs => fn Vrs => fn Map_opt =>
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

        val RVrs_aTs = map (HOLogic.dest_setT o body_type o fastype_of) RVrs;

        val ((((hs, gs), aa), x), _) = lthy
          |> mk_Frees "h" (map (fn a => a --> a) RVrs_aTs)
          ||>> mk_Frees "g" (map fastype_of Injs)
          ||>> mk_Frees "a" (map (domain_type o fastype_of) Injs)
          ||>> apfst hd o mk_Frees "x" [T];
        val frees = inter (op=) Fs (MRBNF_Def.frees_of_mrbnf mrbnf);
        val free = length frees;

        val live = MRBNF_Def.live_of_mrbnf mrbnf;

        val g_prems = map2 (fn Inj => fn g => HOLogic.mk_Trueprop (
          mk_ordLess (mk_card_of (mk_SSupp Inj $ g)) (mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of g))))
        )) Injs gs;
        fun find_f T = List.find (fn f => T = domain_type (fastype_of f)) fs;

        val h_fs = map (the o find_f o domain_type o fastype_of) hs;
        val h_fs_prems = map (HOLogic.mk_Trueprop o mk_supp_bound) h_fs;
        val h_prems = map (HOLogic.mk_Trueprop o mk_supp_bound) hs;

        val map_Inj = map (fn Inj => if body_type (fastype_of Inj) <> T then NONE else
          let
            val a = the (List.find (curry (op=) (domain_type (fastype_of Inj)) o fastype_of) aa);
            val f = the (List.find (curry (op=) (fastype_of a) o domain_type o fastype_of) fs);
            val goal = mk_Trueprop_eq (Term.list_comb (mapx, fs) $ (Inj $ a), Term.subst_atomic_types (lives ~~ lives') Inj $ (f $ a))
            
          in SOME (Goal.prove_sorry lthy (names (fs @ [a])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt trans,
            case #map_Injs axioms of NONE => K all_tac | SOME map_Injs =>
            let
              val mk_id = HOLogic.id_const o domain_type o fastype_of;
              val thm = Local_Defs.unfold0 ctxt @{thms id_o o_id} (
                infer_instantiate' ctxt (map (SOME o Thm.cterm_of lthy) (live_fs @ map mk_id live_fs)) (
                  infer_instantiate' ctxt (map (SOME o Thm.cterm_of lthy) (
                    flat (MRBNF_Def.interlace (replicate live []) (map single bound_fs)
                      (map (single o mk_id) free_fs) (MRBNF_Def.var_types_of_mrbnf mrbnf)
                    ) @ flat (MRBNF_Def.interlace (replicate live []) (map (single o mk_id) bound_fs)
                      (map single free_fs) (MRBNF_Def.var_types_of_mrbnf mrbnf)              
                    )
                  )) (MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym)
                )
              );
              val map_Injs = map (fn thm => @{thm trans[OF comp_apply[symmetric]]} OF [thm RS fun_cong] RS arg_cong) map_Injs;
            in EVERY' [
              rtac ctxt (trans OF [thm]),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
              rtac ctxt trans,
              resolve_tac ctxt map_Injs,
              REPEAT_DETERM o resolve_tac ctxt prems
            ] end,
            rtac ctxt (#map_is_Sb axioms RS fun_cong),
            REPEAT_DETERM o resolve_tac ctxt prems,
            TRY o EVERY' [
              rtac ctxt @{thm trans[OF comp_apply]},
              CHANGED o SELECT_GOAL (Local_Defs.unfold0_tac ctxt (the_default [] (Option.map (fn param =>
                map (fn thm => Local_Defs.unfold0 ctxt @{thms comp_apply} (thm RS fun_cong)) (#Map_Injs param)
              ) bmv_params)))
            ],
            rtac ctxt trans,
            resolve_tac ctxt (map (fn thm => @{thm trans[OF comp_apply[symmetric]]} OF [thm RS fun_cong]) (#Sb_comp_Injs bmv_axioms)),
            REPEAT_DETERM o resolve_tac ctxt (
              @{thms SSupp_comp_bound SSupp_Inj_bound infinite_class.infinite_UNIV card_of_Card_order conjI cinfinite_iff_infinite[THEN iffD2] IImsupp_Inj_comp_bound}
              @ prems @ maps (flat o #Vrs_Injss) (BMV_Monad_Def.axioms_of_bmv_monad bmv)
            ),
            rtac ctxt @{thm comp_apply}
          ])) end
        ) Injs;

        val SSupp_map_subset = @{map 3} (fn Inj => fn g => fn g_prem =>
          let
            val map_t = Term.list_comb (mapx, fs);
            val goal = HOLogic.mk_Trueprop (uncurry mk_leq (
              mk_SSupp (Term.subst_atomic_types (As ~~ As') Inj) $ HOLogic.mk_comp (map_t, g),
              mk_Un (mk_SSupp Inj $ g, mk_supp (the (find_f (domain_type (fastype_of Inj)))))
            ));
          in if body_type (fastype_of map_t) <> body_type (fastype_of (Term.subst_atomic_types (As ~~ As') Inj)) then NONE else
            SOME (Goal.prove_sorry lthy (names (g :: fs)) (f_prems @ [g_prem]) goal (fn {context=ctxt, prems} => EVERY1 [
              rtac ctxt @{thm subsetI},
              EqSubst.eqsubst_tac ctxt [0] @{thms SSupp_def},
              EqSubst.eqsubst_asm_tac ctxt [0] @{thms SSupp_def},
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
        ) Injs gs g_prems;

        val Un_bound = MRBNF_Def.get_class_assumption [BMV_Monad_Def.var_class_of_bmv_monad bmv] "Un_bound" lthy;

        val SSupp_map_bound = @{map 4} (fn Inj => fn g => fn g_prem => Option.map (fn thm =>
          let val goal = HOLogic.mk_Trueprop (uncurry mk_ordLess (
            mk_card_of (mk_SSupp (Term.subst_atomic_types (As ~~ As') Inj) $ HOLogic.mk_comp (Term.list_comb (mapx, fs), g)),
            mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of g)))
          ));
          in Goal.prove_sorry lthy (names (fs @ [g])) (f_prems @ [g_prem]) goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt @{thm card_of_subset_bound},
            rtac ctxt thm,
            REPEAT_DETERM o resolve_tac ctxt prems,
            rtac ctxt Un_bound,
            REPEAT_DETERM o resolve_tac ctxt prems
          ]) end
        )) Injs gs g_prems SSupp_map_subset;

        val Map_map = Option.map (fn Map =>
          let val goal = mk_Trueprop_eq (
            Term.list_comb (Map, map (fn T => the (List.find (curry (op=) T o fastype_of) live_fs)) (fst (split_last (binder_types (fastype_of Map))))),
            MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf) live_fs (map HOLogic.id_const (MRBNF_Def.bounds_of_mrbnf mrbnf)) (map HOLogic.id_const (MRBNF_Def.frees_of_mrbnf mrbnf)) mrbnf
          ) in Goal.prove_sorry lthy (names live_fs) [] goal (fn {context=ctxt, ...} => EVERY1 [
            rtac ctxt sym,
            rtac ctxt trans,
            rtac ctxt (#map_is_Sb axioms),
            REPEAT_DETERM o rtac ctxt @{thm supp_id_bound},
            K (Local_Defs.unfold0_tac ctxt (@{thms id_o o_id} @ no_reflexive [#Sb_Inj bmv_axioms])),
            rtac ctxt refl
          ]) end
        ) Map_opt;

        val SSupp_naturals = @{map_filter 2} (fn Inj => fn g => if body_type (fastype_of Inj) <> T then NONE else
          let
            val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
            val f = the (List.find (curry (op=) (domain_type (fastype_of Inj)) o domain_type o fastype_of) fs);
            val fs = map2 (fn MRBNF_Def.Live_Var => HOLogic.id_const o domain_type o fastype_of | _ => I) var_types fs;
            val map_t = Term.list_comb (Term.subst_atomic_types (As' ~~ As) mapx, fs);
            val goal = mk_Trueprop_eq (
              mk_SSupp Inj $ (HOLogic.mk_comp (HOLogic.mk_comp (map_t, g), mk_inv f)),
              mk_image f $ (mk_SSupp Inj $ g)
            );
            val f_prems = flat (map2 (fn MRBNF_Def.Live_Var => K [] | _ => fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) var_types fs);
          in SOME (Goal.prove_sorry lthy (names (g :: filter_out (fn Const _ => true | _ => false) fs)) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt @{thms SSupp_def}),
            rtac ctxt @{thm set_eqI},
            rtac ctxt iffI,
            K (Local_Defs.unfold0_tac ctxt @{thms mem_Collect_eq comp_apply image_Collect}),
            etac ctxt @{thm contrapos_np},
            dtac ctxt @{thm Meson.not_exD},
            etac ctxt allE,
            dtac ctxt @{thm iffD1[OF de_Morgan_conj]},
            etac ctxt disjE,
            EqSubst.eqsubst_asm_tac ctxt [0] [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f)] @{thm inv_simp2}],
            resolve_tac ctxt prems,
            etac ctxt notE,
            rtac ctxt refl,
            dtac ctxt @{thm notnotD},
            etac ctxt @{thm subst[OF sym]},
            rtac ctxt trans,
            resolve_tac ctxt (map_filter I map_Inj),
            REPEAT_DETERM o resolve_tac ctxt prems,
            EqSubst.eqsubst_tac ctxt [0] [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f)] @{thm inv_simp2}],
            resolve_tac ctxt prems,
            rtac ctxt refl,
            etac ctxt exE,
            etac ctxt conjE,
            hyp_subst_tac ctxt,
            EqSubst.eqsubst_tac ctxt [0] [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f)] @{thm inv_simp1}],
            resolve_tac ctxt prems,
            etac ctxt @{thm contrapos_nn},
            dtac ctxt @{thm trans},
            resolve_tac ctxt (map_filter (Option.map (fn thm =>
              (thm RS sym) OF (flat (fst (fold_map (
                fn MRBNF_Def.Free_Var => apfst tl o chop 2
                | MRBNF_Def.Bound_Var => chop 2
                | _ => pair []
              ) var_types prems)))
            )) map_Inj),
            etac ctxt @{thm injD[rotated]},
            rtac ctxt (MRBNF_Def.inj_map_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_is_inj bij_id} @ prems)
          ])) end
        ) Injs gs;

        val (lsets, bsets, fsets) = MRBNF_Def.deinterlace (MRBNF_Def.sets_of_mrbnf mrbnf) var_types;

        val IImsupp_naturals = @{map_filter 2} (fn Inj => fn g => if body_type (fastype_of Inj) <> T then NONE else SOME (map (fn Vrs =>
          let
            val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
            val f = the (List.find (curry (op=) (domain_type (fastype_of Inj)) o domain_type o fastype_of) fs);
            val f' = the (List.find (curry (op=) (HOLogic.dest_setT (body_type (fastype_of Vrs))) o domain_type o fastype_of) fs);
            val fs = map2 (fn MRBNF_Def.Live_Var => HOLogic.id_const o domain_type o fastype_of | _ => I) var_types fs;
            val map_t = Term.list_comb (Term.subst_atomic_types (As' ~~ As) mapx, fs);
            val goal = mk_Trueprop_eq (
              mk_IImsupp Inj Vrs $ (HOLogic.mk_comp (HOLogic.mk_comp (map_t, g), mk_inv f)),
              mk_image f' $ (mk_IImsupp Inj Vrs $ g)
            );
            val f_prems = flat (map2 (fn MRBNF_Def.Live_Var => K [] | _ => fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) var_types fs);
          in Goal.prove_sorry lthy (names (g :: filter_out (fn Const _ => true | _ => false) fs)) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt @{thms IImsupp_def image_Un image_UN}),
            EqSubst.eqsubst_tac ctxt [0] SSupp_naturals,
            REPEAT_DETERM o resolve_tac ctxt prems,
            K (Local_Defs.unfold0_tac ctxt @{thms image_comp comp_def}),
            EqSubst.eqsubst_tac ctxt [0] @{thms inv_simp1},
            resolve_tac ctxt prems,
            EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt prems,
            rtac ctxt refl
          ]) end
        ) fsets)) Injs gs;

        val IImsupp_Map_bound = @{map_filter 3} (fn Inj => fn g => fn g_prem => if body_type (fastype_of Inj) <> T then NONE else Option.map (fn Map => (map (fn Vrs =>
          let
            val fs = map (fn f_T => the (List.find (curry (op=) f_T o fastype_of) fs))
              (fst (split_last (binder_types (fastype_of Map))));
            val map_t = Term.list_comb (Map, fs);
            val bT = HOLogic.dest_setT (body_type (fastype_of Vrs));
            val card = mk_card_of (HOLogic.mk_UNIV bT);
            val goal = HOLogic.mk_Trueprop (mk_ordLess
              (mk_card_of (Term.subst_atomic_types (lives ~~ lives') (mk_IImsupp Inj Vrs) $ HOLogic.mk_comp (map_t, g)))
              card
            );
            val g_prem = if bT = domain_type (fastype_of Inj) then g_prem else
              HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (mk_IImsupp Inj Vrs $ g)) card);
          in Goal.prove_sorry lthy (names (fs @ [g])) [g_prem] goal (fn {context=ctxt, prems} => EVERY1 [
            K (Local_Defs.unfold_tac ctxt (@{thms IImsupp_Un} @ no_reflexive (#set_Vrs axioms))),
            rtac ctxt @{thm card_of_subset_bound},
            REPEAT_DETERM o rtac ctxt @{thm Un_mono},
            REPEAT_DETERM o resolve_tac ctxt (flat (the_default [] (#IImsupp_Map_subsets bmv_facts))),
            K (Local_Defs.unfold_tac ctxt (@{thms IImsupp_Un[symmetric]} @ map (fn thm => thm RS sym) (no_reflexive (#set_Vrs axioms)))),
            resolve_tac ctxt prems ORELSE' EVERY' [
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms IImsupp_def}),
              rtac ctxt @{thm var_class.UN_bound},
              resolve_tac ctxt prems,
              resolve_tac ctxt (MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf)
            ]
          ]) end
        ) fsets)) Map_opt) Injs gs g_prems;

        val IImsupp_map_bound = @{map_filter 3} (fn Inj => fn g => fn g_prem => if body_type (fastype_of Inj) <> T then NONE else SOME (map (fn Vrs =>
          let
            val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
            val f = the (List.find (curry (op=) (domain_type (fastype_of Inj)) o domain_type o fastype_of) fs);
            val map_t = Term.list_comb (mapx, fs);
            val bT = HOLogic.dest_setT (body_type (fastype_of Vrs));
            val card = mk_card_of (HOLogic.mk_UNIV bT);
            val goal = HOLogic.mk_Trueprop (mk_ordLess
              (mk_card_of (Term.subst_atomic_types (lives ~~ lives') (mk_IImsupp Inj Vrs) $ (HOLogic.mk_comp (HOLogic.mk_comp (map_t, g), mk_inv f))))
              card
            );
            val g_prem = if bT = domain_type (fastype_of Inj) then g_prem else
              HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (mk_IImsupp Inj Vrs $ g)) card);
            val fs' = @{map_filter 2} (fn MRBNF_Def.Live_Var => K NONE | _ => SOME) var_types fs;
            val live_fs = subtract (op=) fs' fs;
            val f_prems = maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) fs';
          in Goal.prove_sorry lthy (names (g :: fs)) (g_prem :: f_prems) goal (fn {context=ctxt, prems} =>
            let val map_comp = Local_Defs.unfold0 ctxt (@{thms id_o o_id}
              @ the_default [] (Option.map (fn thm => [thm RS sym]) Map_map)
            ) (infer_instantiate' ctxt (
              map (SOME o Thm.cterm_of ctxt) fs'
              @ map (SOME o Thm.cterm_of ctxt o HOLogic.id_const o domain_type o fastype_of) fs'
              @ maps (fn f => map (SOME o Thm.cterm_of ctxt) [f, HOLogic.id_const (domain_type (fastype_of f))]) live_fs
            ) (MRBNF_Def.map_comp0_of_mrbnf mrbnf))
            in EVERY1 [
              EqSubst.eqsubst_tac ctxt [0] [map_comp],
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
              K (Local_Defs.unfold0_tac ctxt @{thms comp_assoc}),
              resolve_tac ctxt (flat IImsupp_Map_bound) ORELSE' EVERY' [
                K (Local_Defs.unfold0_tac ctxt (@{thms id_o o_id} @ [MRBNF_Def.map_id0_of_mrbnf mrbnf]))
              ],
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc[symmetric]}),
              EqSubst.eqsubst_tac ctxt [0] (flat IImsupp_naturals @ SSupp_naturals),
              REPEAT_DETERM o resolve_tac ctxt prems,
              rtac ctxt @{thm ordLeq_ordLess_trans[OF card_of_image]},
              REPEAT_DETERM o EVERY' [
                TRY o rtac ctxt @{thm var_class.Un_bound},
                resolve_tac ctxt prems ORELSE' EVERY' [
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms IImsupp_def}),
                  rtac ctxt @{thm var_class.UN_bound},
                  resolve_tac ctxt prems,
                  resolve_tac ctxt (MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf) ORELSE'
                  EVERY' [rtac ctxt @{thm ordLess_ordLeq_trans},
                    resolve_tac ctxt (#Vrs_bds bmv_axioms),
                    rtac ctxt @{thm var_class.large'}
                  ]
                ]
              ]
            ] end
          ) end
        ) fsets)) Injs gs g_prems;

        fun split_Un_bd thm = case try (fn () => thm RS @{thm Un_boundD}) () of
          NONE => [thm] | SOME thm' => split_Un_bd (thm' RS conjunct1) @ [thm' RS conjunct2]

        val IImsupp_map_bound' = map (maps (fn thm => split_Un_bd (
          Local_Defs.unfold lthy (@{thms IImsupp_Un} @ no_reflexive (#set_Vrs axioms)) thm
        ))) IImsupp_map_bound;

        val sets = MRBNF_Def.sets_of_mrbnf mrbnf;
        val (_, bound_sets, _) = MRBNF_Def.deinterlace sets var_types;
        
        val set_Injs = map (fn bset => @{map_filter 2} (fn Inj => fn a =>
          if body_type (fastype_of Inj) <> T then NONE else
            let val goal = mk_Trueprop_eq (bset $ (Inj $ a), mk_bot (HOLogic.dest_setT (body_type (fastype_of bset))))
            in SOME (Goal.prove_sorry lthy (names [a]) [] goal (fn {context=ctxt, ...} => EVERY1 [
              rtac ctxt @{thm ccontr},
              forward_tac ctxt @{thms ex_distinct_bijs},
              resolve_tac ctxt (MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf),
              REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
              Subgoal.FOCUS (fn {context=ctxt, prems, params, ...} =>
                let
                  val mk_id = HOLogic.id_const o domain_type o fastype_of
                  fun mk_map_t g = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
                    (map mk_id live_fs) (map (fn f =>
                      let val T = domain_type (fastype_of f);
                      in if T = HOLogic.dest_setT (body_type (fastype_of bset)) then g else HOLogic.id_const T end
                    ) bound_fs) (map mk_id free_fs) mrbnf;
                  val goal = mk_Trueprop_eq (
                    bset $ (mk_map_t (Thm.term_of (snd (hd params))) $ (Inj $ a)),
                    bset $ (mk_map_t (Thm.term_of (snd (nth params 1))) $ (Inj $ a))
                  );
                  val thm = Goal.prove_sorry ctxt [] [] goal (fn {context=ctxt, ...} => EVERY1 [
                    REPEAT_DETERM o EVERY' [
                      EqSubst.eqsubst_tac ctxt [0] (map (fn thm =>
                        Local_Defs.unfold0 ctxt @{thms comp_apply} (thm RS fun_cong)
                      ) (the (#map_Injs axioms))),
                      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
                      rtac ctxt sym
                    ],
                    rtac ctxt refl
                  ]);
                in EVERY1 [
                  Method.insert_tac ctxt [thm],
                  REPEAT_DETERM_N 2 o EVERY' [
                    EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems)
                  ],
                  etac ctxt @{thm contrapos_pp},
                  resolve_tac ctxt prems
                ] end
              ) ctxt
            ])) end
        ) Injs aa) bound_sets;

      in {
        SSupp_map_subset = SSupp_map_subset,
        SSupp_map_bound = SSupp_map_bound,
        IImsupp_map_bound = IImsupp_map_bound,
        IImsupp_map_bound' = IImsupp_map_bound',
        map_Inj = map_Inj,
        Map_map = Map_map,
        set_Injs = set_Injs
      } end
    ) (BMV_Monad_Def.lives_of_bmv_monad bmv) (BMV_Monad_Def.lives'_of_bmv_monad bmv)
      axioms' mrbnfs (BMV_Monad_Def.axioms_of_bmv_monad bmv) (BMV_Monad_Def.params_of_bmv_monad bmv) (BMV_Monad_Def.facts_of_bmv_monad bmv)
      (BMV_Monad_Def.Sbs_of_bmv_monad bmv) (BMV_Monad_Def.Injs_of_bmv_monad bmv)
      (BMV_Monad_Def.RVrs_of_bmv_monad bmv) (BMV_Monad_Def.Vrs_of_bmv_monad bmv) (BMV_Monad_Def.Maps_of_bmv_monad bmv);

    val facts' = @{map 10} (fn i => fn axioms => fn facts => fn mrbnf => fn bmv_axioms => fn bmv_params => fn bmv_facts => fn Sb => fn RVrs => fn Injs =>
      let
        val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
        val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
        val live = MRBNF_Def.live_of_mrbnf mrbnf;

        val T = body_type (fastype_of Sb);
        val fs = map (fn T => the (List.find (curry (op=) T o fastype_of) fs)) (fst (split_last (binder_types (fastype_of mapx))));
        val (live_fs, bound_fs, free_fs) = MRBNF_Def.deinterlace fs var_types;

        val RVrs_aTs = map (HOLogic.dest_setT o body_type o fastype_of) RVrs;

        val ((((hs, gs), aa), x), _) = lthy
          |> mk_Frees "h" (map (fn a => a --> a) RVrs_aTs)
          ||>> mk_Frees "g" (map fastype_of Injs)
          ||>> mk_Frees "a" (map (domain_type o fastype_of) Injs)
          ||>> apfst hd o mk_Frees "x" [T];
        val frees = inter (op=) Fs (MRBNF_Def.frees_of_mrbnf mrbnf);
        val free = length frees;

        (*val g_prems = map2 (fn Inj => fn g => HOLogic.mk_Trueprop (
          mk_ordLess (mk_card_of (mk_SSupp Inj $ g)) (mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of g))))
        )) Injs gs;*)
        val small_prems = flat (BMV_Monad_Def.mk_small_prems_of_bmv_monad bmv i hs gs);

        fun find_f T = List.find (curry (op=) T o domain_type o fastype_of) fs;
        (*val h_prems = map (HOLogic.mk_Trueprop o mk_supp_bound) hs;*)
        val h_fs = map (the o find_f o domain_type o fastype_of) hs;

        val map_Sb_strong =
          let
            val map_t = Term.list_comb (mapx, fs);
            val mrbnfs' = map (fn Inj =>
              the (List.find (fn mrbnf => body_type (fastype_of (MRBNF_Def.map_of_mrbnf mrbnf)) = body_type (fastype_of (Term.subst_atomic_types (As ~~ As') Inj))) mrbnfs)
            ) Injs;
            val goal = mk_Trueprop_eq (
              HOLogic.mk_comp (map_t, Term.list_comb (Sb, hs @ gs)),
              HOLogic.mk_comp (Term.list_comb (Term.subst_atomic_types (As ~~ As') Sb,
                map2 (fn h => fn f => HOLogic.mk_comp (HOLogic.mk_comp (f, h), mk_inv f)) hs h_fs @
                map2 (fn g => fn mrbnf =>
                let val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
                in HOLogic.mk_comp (HOLogic.mk_comp (
                  Term.list_comb (mapx,
                    map (the o find_f o domain_type) (fst (split_last (binder_types (fastype_of mapx))))
                  ),
                  g), mk_inv (the (find_f (domain_type (fastype_of g))))
                ) end
              ) gs mrbnfs'), map_t)
            );

            val f_prems = flat (MRBNF_Def.interlace (replicate live [])
              (map (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) bound_fs)
              (map (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) free_fs) var_types);
            val id_of_f = HOLogic.id_const o domain_type o fastype_of
            val count = live + MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.free_of_mrbnf mrbnf - free;
            val map_is_Sb = filter_out (
              (op=) o HOLogic.dest_eq o HOLogic.dest_Trueprop o snd o Logic.strip_horn o Thm.prop_of
            ) (map #map_is_Sb axioms');

            val IImsupp_map_bound' = map (fn thm => Local_Defs.unfold0 lthy @{thms inv_id id_o o_id} (thm OF (@{thm _}::
              maps (fn MRBNF_Def.Free_Var => @{thms bij_id supp_id_bound}
                | MRBNF_Def.Bound_Var => @{thms _ _}
                | _ => []
              ) (MRBNF_Def.var_types_of_mrbnf mrbnf))
            )) (flat (#IImsupp_map_bound facts));

          in Goal.prove_sorry lthy (names (fs @ hs @ gs)) (f_prems @ small_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
            rtac ctxt refl
          ] ORELSE EVERY1 [
            rtac ctxt trans,
            rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
            let val comp_tac = EVERY' [
              if count > 0 then EVERY' [
                rtac ctxt trans,
                rtac ctxt (Local_Defs.unfold0 ctxt @{thms id_o o_id} (infer_instantiate' ctxt (
                    map (SOME o Thm.cterm_of ctxt) (flat (
                    MRBNF_Def.interlace (replicate (2 * live) [])
                      (map single bound_fs @ map (single o id_of_f) bound_fs)
                      (map (single o id_of_f) free_fs @ map single free_fs) (var_types @ var_types)
                  ) @ maps (fn f => [f, HOLogic.id_const (domain_type (fastype_of f))]) live_fs)
                ) (MRBNF_Def.map_comp0_of_mrbnf mrbnf))),
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
                rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]}
              ] else K all_tac,
              rtac ctxt (#map_is_Sb axioms),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
              K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id})
            ] in EVERY' [
              comp_tac,
              rtac ctxt sym,
              rtac ctxt trans,
              rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
              comp_tac
            ] end,
            rtac ctxt sym,
            EVERY' [
              rtac ctxt trans,
              rtac ctxt @{thm trans[OF comp_assoc]},
              if MRBNF_Def.live_of_mrbnf mrbnf = 0 then K all_tac else EVERY' [
                rtac ctxt @{thm trans[OF comp_assoc]},
                rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]}
              ],
              rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
              resolve_tac ctxt (the_default [] (Option.map single (#map_Sb axioms))),
              REPEAT_DETERM o resolve_tac ctxt prems,
              if MRBNF_Def.live_of_mrbnf mrbnf = 0 then K all_tac else EVERY' [
                rtac ctxt trans,
                rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
                rtac ctxt @{thm trans[OF comp_assoc[symmetric]]},
                rtac ctxt trans,
                rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
                rtac ctxt (#Map_Sb (the bmv_params))
                THEN_ALL_NEW (SELECT_GOAL (
                REPEAT_DETERM (HEADGOAL (resolve_tac ctxt (@{thms supp_id_bound}
                  @ prems @ IImsupp_map_bound'
                  @ maps (map_filter I o #SSupp_map_bound) facts'
                ) ORELSE' (CHANGED o SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms id_o o_id} @
                  [MRBNF_Def.map_id0_of_mrbnf mrbnf]
                ))))))),
                rtac ctxt @{thm comp_assoc}
              ],
              rtac ctxt @{thm trans[OF comp_assoc[symmetric]]},
              rtac ctxt trans,
              rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]}
            ] ORELSE' rtac ctxt trans,
            rtac ctxt (#Sb_comp bmv_axioms)
            THEN_ALL_NEW (SELECT_GOAL (REPEAT_DETERM (FIRST1 [
              EVERY' [
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms comp_assoc id_o o_id} @ [
                  MRBNF_Def.map_id0_of_mrbnf mrbnf
                ])),
                resolve_tac ctxt (
                  @{thms supp_id_bound supp_comp_bound supp_inv_bound infinite_class.infinite_UNIV
                    SSupp_comp_bound SSupp_Inj_bound card_of_Card_order conjI
                    cinfinite_iff_infinite[THEN iffD2] IImsupp_Inj_comp_bound
                  }
                  @ prems @ maps (the_default [] o #SSupp_Map_bounds) (BMV_Monad_Def.facts_of_bmv_monad bmv)
                  @ maps (flat o the_default [] o #IImsupp_Map_bounds) (BMV_Monad_Def.facts_of_bmv_monad bmv)
                  @ maps (map_filter I o #SSupp_map_bound) facts'
                  @ maps (flat o #Vrs_Injss) (BMV_Monad_Def.axioms_of_bmv_monad bmv)
                  @ IImsupp_map_bound'
                )
              ]
            ]))),
            rtac ctxt sym,
            rtac ctxt trans,
            TRY o EVERY' [
              rtac ctxt @{thm trans[OF comp_assoc[symmetric]]},
              rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
              if MRBNF_Def.live_of_mrbnf mrbnf = 0 then K all_tac else EVERY' [
                rtac ctxt @{thm trans[OF comp_assoc[symmetric]]},
                rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]}
              ]
            ],
            rtac ctxt (#Sb_comp bmv_axioms),
            REPEAT_DETERM o FIRST' [
              EVERY' [
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc[symmetric]}),
                resolve_tac ctxt (maps (flat o #IImsupp_map_bound) facts' @ maps (flat o #IImsupp_map_bound') facts')
              ],
              EVERY' [
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms comp_assoc id_o o_id} @ [
                  MRBNF_Def.map_id0_of_mrbnf mrbnf
                ])),
                resolve_tac ctxt (
                  @{thms supp_id_bound supp_comp_bound supp_inv_bound infinite_class.infinite_UNIV
                    SSupp_comp_bound SSupp_Inj_bound card_of_Card_order conjI
                    cinfinite_iff_infinite[THEN iffD2] IImsupp_Inj_comp_bound var_class.Un_bound
                  }
                  @ prems @ maps (the_default [] o #SSupp_Map_bounds) (BMV_Monad_Def.facts_of_bmv_monad bmv)
                  @ maps (flat o the_default [] o #IImsupp_Map_bounds) (BMV_Monad_Def.facts_of_bmv_monad bmv)
                  @ maps (map_filter I o #SSupp_map_bound) facts'
                  @ maps (flat o #Vrs_Injss) (BMV_Monad_Def.axioms_of_bmv_monad bmv)
                  @ IImsupp_map_bound'
                )
              ]
            ],
            TRY o rtac ctxt @{thm trans[OF comp_assoc]},
            TRY o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
            rtac ctxt ext,
            rtac ctxt (#Sb_cong bmv_axioms),
            REPEAT_DETERM o FIRST' [
              EVERY' [
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc[symmetric]}),
                resolve_tac ctxt (maps (flat o #IImsupp_map_bound) facts' @ maps (flat o #IImsupp_map_bound') facts')
              ],
              EVERY' [
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms comp_assoc id_o o_id} @ [
                  MRBNF_Def.map_id0_of_mrbnf mrbnf
                ])),
                resolve_tac ctxt (
                  @{thms supp_id_bound supp_comp_bound supp_inv_bound infinite_class.infinite_UNIV SSupp_comp_bound
                  SSupp_Inj_bound card_of_Card_order conjI cinfinite_iff_infinite[THEN iffD2] IImsupp_Inj_comp_bound var_class.Un_bound}
                  @ flat (#IImsupp_map_bound facts)
                  @ prems @ maps (the_default [] o #SSupp_Map_bounds) (BMV_Monad_Def.facts_of_bmv_monad bmv)
                  @ maps (flat o the_default [] o #IImsupp_Map_bounds) (BMV_Monad_Def.facts_of_bmv_monad bmv)
                  @ maps (map_filter I o #SSupp_map_bound) facts'
                  @ maps #SSupp_Sb_bounds (BMV_Monad_Def.facts_of_bmv_monad bmv)
                  @ maps (flat o #IImsupp_Sb_boundss) (BMV_Monad_Def.facts_of_bmv_monad bmv)
                  @ maps (flat o #Vrs_Injss) (BMV_Monad_Def.axioms_of_bmv_monad bmv)
                  @ IImsupp_map_bound'
                )
              ]
            ],
            (* renaming-only subst functions *)
            REPEAT_DETERM o EVERY' [
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc}),
              EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
              resolve_tac ctxt prems,
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms o_id}),
              rtac ctxt refl
            ],
            REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
              rtac ctxt trans,
              rtac ctxt @{thm trans[OF comp_assoc[symmetric], THEN fun_cong]},
              rtac ctxt trans,
              rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
              resolve_tac ctxt (maps #Sb_comp_Injs (BMV_Monad_Def.axioms_of_bmv_monad bmv)),
              REPEAT_DETERM o FIRST' [
                EVERY' [
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc[symmetric]}),
                  resolve_tac ctxt (maps (flat o #IImsupp_map_bound) facts' @ maps (flat o #IImsupp_map_bound') facts')
                ],
                EVERY' [
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms comp_assoc id_o o_id} @ [
                    MRBNF_Def.map_id0_of_mrbnf mrbnf
                  ])),
                  resolve_tac ctxt (
                    @{thms supp_id_bound supp_comp_bound supp_inv_bound infinite_class.infinite_UNIV
                      SSupp_comp_bound SSupp_Inj_bound card_of_Card_order conjI
                      cinfinite_iff_infinite[THEN iffD2] IImsupp_Inj_comp_bound var_class.Un_bound
                    }
                    @ prems @ maps (the_default [] o #SSupp_Map_bounds) (BMV_Monad_Def.facts_of_bmv_monad bmv)
                    @ maps (flat o the_default [] o #IImsupp_Map_bounds) (BMV_Monad_Def.facts_of_bmv_monad bmv)
                    @ maps (map_filter I o #SSupp_map_bound) facts'
                    @ maps (flat o #Vrs_Injss) (BMV_Monad_Def.axioms_of_bmv_monad bmv)
                    @ IImsupp_map_bound'
                  )
                ]
              ],
              rtac ctxt @{thm trans[OF comp_assoc]},
              rtac ctxt trans,
              rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
              rtac ctxt @{thm inv_o_simp1},
              resolve_tac ctxt prems,
              rtac ctxt @{thm o_id},
              rtac ctxt sym,
              rtac ctxt trans,
              EVERY' [
                resolve_tac ctxt @{thms arg_cong2[OF _ refl, of _ _ "(\<circ>)"] arg_cong2[OF _ refl, of _ _ "(\<circ>)", THEN fun_cong]},
                resolve_tac ctxt (map (fn thm => thm RS sym) map_is_Sb)
              ] ORELSE' EVERY' [
                rtac ctxt @{thm trans[OF comp_assoc[symmetric], THEN fun_cong]},
                resolve_tac ctxt @{thms arg_cong2[OF _ refl, of _ _ "(\<circ>)"] arg_cong2[OF _ refl, of _ _ "(\<circ>)", THEN fun_cong]},
                resolve_tac ctxt (map (fn thm => thm RS sym) map_is_Sb)
              ],
              REPEAT_DETERM o resolve_tac ctxt prems,
              rtac ctxt refl ORELSE' EVERY' [
                rtac ctxt trans,
                rtac ctxt @{thm trans[OF comp_assoc[symmetric], THEN fun_cong]},
                rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
                resolve_tac ctxt (map (fn mrbnf => MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym) mrbnfs),
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
                K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
                rtac ctxt refl
              ]
            ])
          ]) end;
      in {
        SSupp_map_subset = #SSupp_map_subset facts,
        SSupp_map_bound = #SSupp_map_bound facts,
        map_Inj = #map_Inj facts,
        map_Sb_strong = map_Sb_strong,
        Map_map = #Map_map facts,
        set_Injs = #set_Injs facts
      }: mrsbnf_facts end
    ) (0 upto length axioms' - 1) axioms' facts' mrbnfs (BMV_Monad_Def.axioms_of_bmv_monad bmv) (BMV_Monad_Def.params_of_bmv_monad bmv) (BMV_Monad_Def.facts_of_bmv_monad bmv)
      (BMV_Monad_Def.Sbs_of_bmv_monad bmv) (BMV_Monad_Def.RVrs_of_bmv_monad bmv)
      (BMV_Monad_Def.Injs_of_bmv_monad bmv);

    val mrsbnf = MRSBNF {
      mrbnfs = mrbnfs,
      pbmv_monad = bmv,
      axioms = axioms',
      facts = facts'
    };

    val mrsbnf = morph_mrsbnf (MRBNF_Util.subst_typ_morphism (
      map (fn T => (T, Logic.varifyT_global T)) (deads @ As @ As' @ Bs @ Fs)
    )) mrsbnf;
  in (mrsbnf, lthy) end;

fun mk_mrsbnf_axioms mrbnfs bmv lthy =
  let
    val l = BMV_Monad_Def.leader_of_bmv_monad bmv;
    val lmrbnf = nth mrbnfs l;
    val ldeads = distinct (op=) (filter_out Term.is_Type (MRBNF_Def.deads_of_mrbnf lmrbnf));

    val (((((Fs, Bs), As), As'), deads), names_lthy) = lthy
      |> mk_TFrees' (map Type.sort_of_atyp (MRBNF_Def.frees_of_mrbnf lmrbnf))
      ||>> mk_TFrees' (map Type.sort_of_atyp (MRBNF_Def.bounds_of_mrbnf lmrbnf))
      ||>> mk_TFrees (MRBNF_Def.live_of_mrbnf lmrbnf)
      ||>> mk_TFrees (MRBNF_Def.live_of_mrbnf lmrbnf)
      ||>> mk_TFrees' (map Type.sort_of_atyp ldeads);

    val (fs, names_lthy) = names_lthy
      |> mk_Frees "f" (MRBNF_Def.interlace (map2 (curry (op-->)) As As') (map (fn a => a --> a) Bs) (map (fn a => a --> a) Fs) (MRBNF_Def.var_types_of_mrbnf lmrbnf));

    local
      val subst =
        (MRBNF_Def.frees_of_mrbnf lmrbnf ~~ Fs)
        @ (MRBNF_Def.bounds_of_mrbnf lmrbnf ~~ Bs)
        @ (MRBNF_Def.lives_of_mrbnf lmrbnf ~~ As)
        @ (MRBNF_Def.lives'_of_mrbnf lmrbnf ~~ As')
        @ (ldeads ~~ deads)
      val phi = MRBNF_Util.subst_typ_morphism subst;
    in
      val mrbnfs = map (MRBNF_Def.morph_mrbnf phi) mrbnfs;
      val bmv = BMV_Monad_Def.morph_bmv_monad phi bmv;
    end;

    val axioms = @{map 7} (fn mrbnf => fn Sb => fn Injs => fn RVrs => fn Vrs => fn Map_opt => fn lives =>
      let
        val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
        val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;

        val fs = map (fn T => the (List.find (curry (op=) T o fastype_of) fs)) (fst (split_last (binder_types (fastype_of mapx))));

        val (live_fs, bound_fs, free_fs') = MRBNF_Def.deinterlace fs var_types;

        val frees = inter (op=) (take (length (leader BMV_Monad_Def.frees_of_bmv_monad bmv)) Fs) (MRBNF_Def.frees_of_mrbnf mrbnf);
        val pfrees = subtract (op=) frees (MRBNF_Def.frees_of_mrbnf mrbnf);

        val free = length frees;
        val free_fs = take free free_fs';

        val free_prems = map (HOLogic.mk_Trueprop o mk_supp_bound) free_fs;
        val live_fs' = filter (member (op=) lives o domain_type o fastype_of) live_fs;

        val map_is_Sb = fold_rev Logic.all (free_fs @ live_fs') (fold_rev (curry Logic.mk_implies) free_prems (mk_Trueprop_eq (
          Term.list_comb (Term.subst_atomic_types (filter_out (member (op=) lives o snd) (As' ~~ As)) mapx, MRBNF_Def.interlace
            (map (fn a => the_default (HOLogic.id_const a) (
              List.find (curry (op=) a o domain_type o fastype_of) live_fs'
            )) As) (map HOLogic.id_const Bs) (free_fs @ map HOLogic.id_const (drop (length frees) Fs))
            (MRBNF_Def.var_types_of_mrbnf mrbnf)
          ),
          let val add_Map = case Map_opt of
            NONE => I
            | SOME Map => fn t => HOLogic.mk_comp (Term.subst_atomic_types (filter (member (op=) lives o fst) (As ~~ As')) t,
              Term.list_comb (Map, map (fn T =>
                the (List.find (curry (op=) T o fastype_of) live_fs')
              ) (fst (split_last (binder_types (fastype_of Map)))))
            )
          in add_Map (Term.list_comb (Sb, map (fn RVr => the (List.find (fn f =>
              HOLogic.dest_setT (body_type (fastype_of RVr)) = domain_type (fastype_of f)
            ) fs)) RVrs @ map (fn Inj =>
              HOLogic.mk_comp (Inj, the (List.find (fn f => (op=) (apply2 (domain_type o fastype_of) (Inj, f))) fs))
            ) Injs)
          ) end
        )));

        val RVrs_aTs = map (HOLogic.dest_setT o body_type o fastype_of) RVrs;

        val (((gs, hs), x), _) = names_lthy
          |> mk_Frees "g" (map fastype_of Injs)
          ||>> mk_Frees "h" (map (fn a => a --> a) RVrs_aTs)
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

        val g_prems = map2 (fn Inj => fn g => HOLogic.mk_Trueprop (uncurry mk_ordLess (
          mk_card_of (mk_SSupp Inj $ g), mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of g)))
        ))) Injs gs;
        val h_prems = map (HOLogic.mk_Trueprop o mk_supp_bound) hs;

        val count = live + MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf;
        val map_Sb = if count - free = 0 then NONE else
          let
            val map_t = Term.list_comb (mapx, MRBNF_Def.interlace live_fs bound_fs (map HOLogic.id_const frees @ pfree_fs) var_types);
            val Sb_t = Term.list_comb (Sb, hs @ gs);
          in SOME (fold_rev Logic.all (other_fs @ hs @ gs) (fold_rev (curry Logic.mk_implies) (other_prems @ h_prems @ g_prems) (mk_Trueprop_eq (
            HOLogic.mk_comp (map_t, Sb_t),
            HOLogic.mk_comp (Term.list_comb (Term.subst_atomic_types (As ~~ As') Sb, hs @ map (fn g =>
              let
                val mapx = Option.map MRBNF_Def.map_of_mrbnf (
                  List.find (curry (op=) (body_type (fastype_of g)) o MRBNF_Def.T_of_mrbnf) mrbnfs
                );
                val add_map = case mapx of
                  NONE => I
                  | SOME mapx => fn t =>
                    let val fs = map (fn T => the_default (HOLogic.id_const T) (
                      List.find (curry (op=) T o domain_type o fastype_of) other_fs
                    )) (map domain_type (fst (split_last (binder_types (fastype_of mapx)))))
                    in if forall (fn Const (@{const_name id}, _) => true | _ => false) fs then t else
                      HOLogic.mk_comp (Term.list_comb (mapx, fs), t)
                    end
              in add_map g end
            ) gs), map_t)
          )))) end;

        val sets = MRBNF_Def.sets_of_mrbnf mrbnf;
        val (live_sets, bound_sets, free_sets) = MRBNF_Def.deinterlace sets var_types;

        val set_Sbs =
          let
            val sets' = flat (MRBNF_Def.interlace (map single live_sets) (map single bound_sets)
              (replicate free [] @ map single (drop free free_sets)) var_types);
          in map (fn set => fold_rev Logic.all (hs @ gs @ [x]) (fold_rev (curry Logic.mk_implies) (h_prems @ g_prems) (
            mk_Trueprop_eq (set $ (Term.list_comb (Sb, hs @ gs) $ x), foldl1 mk_Un ((set $ x) ::
              @{map_filter 2} (fn Vrs => fn g => Option.mapPartial (fn mrbnf => Option.map (fn set =>
                mk_UNION (Vrs $ x) (Term.abs ("x", HOLogic.dest_setT (body_type (fastype_of Vrs))) (
                  set $ (g $ Bound 0)
                ))
              ) (List.find (curry (op=) (body_type (fastype_of set)) o body_type o fastype_of) (MRBNF_Def.sets_of_mrbnf mrbnf)))
                (List.find (curry (op=) (body_type (fastype_of g)) o MRBNF_Def.T_of_mrbnf) mrbnfs)
            ) Vrs gs))
          ))) sets' end;

        val set_Vrs = map (fn set =>
          let
            val aT = HOLogic.dest_setT (fastype_of (set $ x));
            val Vrs = filter (curry (op=) aT o HOLogic.dest_setT o body_type o fastype_of) (RVrs @ Vrs);
            val Vrs' = map (fn Vrs => Vrs $ x) Vrs;
          in Logic.all x (mk_Trueprop_eq (set $ x, case Vrs' of
            [] => mk_bot aT
            | _ => foldl1 mk_Un Vrs'
          )) end
        ) (take free free_sets);

        val map_Injs = if MRBNF_Def.bound_of_mrbnf mrbnf = 0 then NONE else SOME (map_filter (fn Inj =>
          if body_type (fastype_of Inj) <> body_type (fastype_of Sb) then NONE else
            let
              val mk_ids = map (HOLogic.id_const o domain_type o fastype_of);
              val map_t = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf) (mk_ids live_fs) bound_fs (mk_ids free_fs') mrbnf;
              val goal = fold_rev Logic.all bound_fs (fold_rev (curry Logic.mk_implies) (maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) bound_fs) (
                mk_Trueprop_eq (HOLogic.mk_comp (map_t, Inj), Inj)
              ));
            in SOME goal end
        ) Injs)
      in {
        map_is_Sb = map_is_Sb,
        map_Injs = map_Injs,
        set_Vrs = set_Vrs,
        map_Sb = map_Sb,
        set_Sb = set_Sbs
      }: term mrsbnf_axioms end
    ) mrbnfs
      (BMV_Monad_Def.Sbs_of_bmv_monad bmv) (BMV_Monad_Def.Injs_of_bmv_monad bmv)
      (BMV_Monad_Def.RVrs_of_bmv_monad bmv)
      (BMV_Monad_Def.Vrs_of_bmv_monad bmv) (BMV_Monad_Def.Maps_of_bmv_monad bmv) (BMV_Monad_Def.lives_of_bmv_monad bmv);
  in (axioms, (deads, As, As', Bs, Fs, fs), mrbnfs, bmv) end

fun prove_axioms mrbnfs bmv tacs lthy =
  let
    val (goals, vars, mrbnfs, bmv) = mk_mrsbnf_axioms mrbnfs bmv lthy;
    val tacs' = map (map_mrsbnf_axioms (fn tac => fn goal => Goal.prove_sorry lthy [] [] goal (tac o #context))) tacs;
    val _ = if length tacs' = length goals then () else
      error ("Expected " ^ string_of_int (length goals) ^ " sets of axiom tactics, but got " ^ string_of_int (length tacs'))
  in (map2 apply_mrsbnf_axioms tacs' goals, vars, mrbnfs, bmv) end

fun mrsbnf_def fact_policy qualify name_opt mrbnfs bmv tacs lthy =
  let
    val (axioms, vars, mrbnfs, bmv) = prove_axioms mrbnfs bmv tacs lthy;
  in mk_mrsbnf fact_policy qualify vars name_opt mrbnfs bmv axioms lthy end

fun mrsbnf_of_mrbnf mrbnf lthy =
  let
    val (bmv, lthy) = BMV_Monad_Def.pbmv_monad_of_mrbnf mrbnf lthy;
    val bmv_vars = BMV_Monad_Def.lives_of_bmv_monad bmv @ BMV_Monad_Def.lives'_of_bmv_monad bmv
        @ BMV_Monad_Def.frees_of_bmv_monad bmv @ BMV_Monad_Def.deads_of_bmv_monad bmv;
    val bmv = BMV_Monad_Def.morph_bmv_monad (MRBNF_Util.subst_typ_morphism (map (fn a => (a, Logic.varifyT_global a)) (flat bmv_vars))) bmv;
    val n = MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.live_of_mrbnf mrbnf;

    val bmv =
      let
        val tyenv = fold (Sign.typ_match (Proof_Context.theory_of lthy))
          ((hd (BMV_Monad_Def.ops_of_bmv_monad bmv), MRBNF_Def.T_of_mrbnf mrbnf)
          :: the_default [] (Option.map (fn Map =>
            [(body_type (fastype_of Map), body_type (fastype_of (MRBNF_Def.map_of_mrbnf mrbnf)))]
          ) (hd (BMV_Monad_Def.Maps_of_bmv_monad bmv))
        )) Vartab.empty;
        val phi = MRBNF_Util.subst_typ_morphism (map (fn (x, (s, T)) => (TVar (x, s), T)) (Vartab.dest tyenv))
      in BMV_Monad_Def.morph_bmv_monad phi bmv end;
  in mrsbnf_def (K BNF_Def.Dont_Note) I NONE [mrbnf] bmv [{
    map_Sb = SOME (fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (@{thms id_o o_id} @ unfolds_of_bmv_monad bmv)),
      rtac ctxt refl ORELSE' EVERY' [
        rtac ctxt (trans OF [MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym]),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
        rtac ctxt sym,
        rtac ctxt (trans OF [MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym]),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
        K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
        rtac ctxt refl
      ]
    ]),
    map_is_Sb = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (unfolds_of_bmv_monad bmv)),
      TRY o EVERY' [
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt (MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
      ],
      K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
      resolve_tac ctxt [refl, MRBNF_Def.map_id0_of_mrbnf mrbnf]
    ],
    map_Injs = if MRBNF_Def.bound_of_mrbnf mrbnf = 0 then NONE else SOME [],
    set_Sb = replicate n (fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (@{thms id_apply} @ unfolds_of_bmv_monad bmv)),
      rtac ctxt refl ORELSE' EVERY' [
        rtac ctxt trans,
        resolve_tac ctxt (MRBNF_Def.set_map_of_mrbnf mrbnf),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
        rtac ctxt @{thm image_id}
      ]
    ]),
    set_Vrs = replicate (MRBNF_Def.free_of_mrbnf mrbnf) (fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (unfolds_of_bmv_monad bmv)),
      rtac ctxt refl
    ])
  }] lthy end;

fun mrsbnf_cmd b_Ts lthy =
  let
    val Ts = map (Syntax.read_typ lthy o snd) b_Ts;
    val ancestors = map Context.theory_base_name (
      Context.ancestors_of (Proof_Context.theory_of lthy)
    );
    val b = fst (hd b_Ts);
    val name = if Binding.is_empty b then fst (dest_Type (hd Ts)) else Local_Theory.full_name lthy b;
    fun find_bmv [] = error ("Type " ^ name ^ " is not a PBMV Monad")
      | find_bmv (x::xs) = (case BMV_Monad_Def.pbmv_monad_of lthy (Binding.name_of (Binding.prefix_name (x ^ ".") b)) of
        NONE => find_bmv xs
        | SOME bmv => bmv)
    fun find_mrbnf [] = NONE
      | find_mrbnf (x::xs) = (case MRBNF_Def.mrbnf_of lthy (Binding.name_of (Binding.prefix_name (x ^ ".") b)) of
        NONE => find_mrbnf xs
        | SOME mrbnf => SOME mrbnf)

    val (mrbnfs, lthy) = @{fold_map 2} (fn T => fn b => fn lthy =>
      let
        val name = if Binding.is_empty b then fst (dest_Type T) else Local_Theory.full_name lthy b;
        val (mrbnf, lthy) = case MRBNF_Def.mrbnf_of lthy name of
          SOME mrbnf => (SOME mrbnf, lthy)
          | NONE => case BNF_Def.bnf_of lthy name of
            SOME bnf => apfst SOME (MRBNF_Def.mrbnf_of_bnf bnf lthy)
            | NONE => (find_mrbnf ancestors, lthy)
        val mrbnf = case mrbnf of SOME mrbnf => mrbnf | NONE => error ("Type " ^ name ^ " is not a (MR)BNF")
      in (mrbnf, lthy) end
    ) Ts (map fst b_Ts) lthy;
    val bmv_monad = case BMV_Monad_Def.pbmv_monad_of lthy name of
      SOME bmv => bmv
      | NONE => find_bmv ancestors

    val mrbnfs = @{map 3} (fn T => fn Map_opt => fn mrbnf =>
      let
        val xs = case Map_opt of
          NONE => [(MRBNF_Def.T_of_mrbnf mrbnf, T)]
          | SOME Map => let
            fun get_T t = (snd (split_last (binder_types (fastype_of t))), body_type (fastype_of t))
            val T = get_T Map
            val T' = get_T (MRBNF_Def.map_of_mrbnf mrbnf)
          in [(fst T', fst T), (snd T', snd T)] end
        val tyenv = fold (Sign.typ_match (Proof_Context.theory_of lthy)) xs Vartab.empty;
        val phi = MRBNF_Util.subst_typ_morphism (map (fn (x, (s, T)) => (TVar (x, s), T)) (Vartab.dest tyenv));
      in MRBNF_Def.morph_mrbnf phi mrbnf end
    ) (BMV_Monad_Def.ops_of_bmv_monad bmv_monad) (BMV_Monad_Def.Maps_of_bmv_monad bmv_monad) mrbnfs;

    val (goals, vars, mrbnfs, bmv) = mk_mrsbnf_axioms mrbnfs bmv_monad lthy;

    fun after_qed thmss lthy =
      let
        val thms = map hd thmss;

        fun chop_opt _ NONE thms = (NONE, thms)
          | chop_opt n (SOME _) thms = (SOME (take n thms), drop n thms)

        val axioms = fst (fold_map (fn goals => fn thms =>
          let val (((((map_is_Sb, map_Sb), map_Injs), set_Vrs), set_Sb), thms) = thms
            |> apfst hd o chop 1
            ||>> apfst (Option.map hd) o chop_opt 1 (#map_Sb goals)
            ||>> chop_opt (the_default 0 (Option.map length (#map_Injs goals))) (#map_Injs goals)
            ||>> chop (length (#set_Vrs goals))
            ||>> chop (length (#set_Sb goals));
          in ({
            map_is_Sb = map_is_Sb,
            map_Sb = map_Sb,
            map_Injs = map_Injs,
            set_Vrs = set_Vrs,
            set_Sb = set_Sb
          }: thm mrsbnf_axioms, thms) end
        ) goals thms);

        val (mrsbnf, lthy) = mk_mrsbnf (K BNF_Def.Note_Some) I vars (SOME name) mrbnfs bmv axioms lthy;
        val (_, lthy) = note_mrsbnf_thms (K BNF_Def.Note_Some) I (SOME name) mrsbnf lthy;
        val lthy = register_mrsbnf name mrsbnf lthy;
      in lthy end

  in Proof.theorem NONE after_qed (map (single o rpair []) (maps (fn goals =>
    #map_is_Sb goals :: the_default [] (Option.map single (#map_Sb goals)) @ the_default [] (#map_Injs goals)
    @ #set_Vrs goals @  #set_Sb goals
  ) goals)) lthy
    |> Proof.unfolding ([[(
      BMV_Monad_Def.unfolds_of_bmv_monad bmv
      @ map MRBNF_Def.map_def_of_mrbnf mrbnfs
      @ maps MRBNF_Def.set_defs_of_mrbnf mrbnfs
    , [])]])
    |> Proof.refine_singleton (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (TRYALL (rtac ctxt refl))))
  end

val _ = Outer_Syntax.local_theory_to_proof @{command_keyword mrsbnf}
  "register a map-restricted substitutive bounded natural functor"
  ((Parse.and_list1 (parse_opt_binding_colon -- Parse.typ)) >> mrsbnf_cmd)

end