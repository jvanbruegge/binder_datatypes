signature BMV_MONAD_DEF = sig
  type bmv_monad

  type 'a supported_functor_axioms = {
    Map_id: 'a,
    Map_comp: 'a,
    Supp_Map: 'a list,
    Supp_bd: 'a list,
    Map_cong: 'a
  };

  type 'a bmv_monad_axioms = {
    Sb_Inj: 'a,
    Sb_comp_Injs: 'a list,
    Sb_comp: 'a,
    Sb_cong: 'a,
    Vrs_bds: 'a option list list,
    Vrs_Injs: 'a option list list,
    Vrs_Sbs: 'a option list list
  };

  type 'a bmv_monad_param = {
    Map: term,
    Supps: term list,
    axioms: 'a supported_functor_axioms,
    Map_Sb: 'a,
    Supp_Sb: 'a list,
    Map_Vrs: 'a option list list
  };

  type 'a bmv_monad_model = {
    ops: typ list,
    bd: term,
    var_class: class,
    bmv_ops: bmv_monad list,
    frees: typ list,
    leader: int,
    lives: typ list,
    lives': typ list,
    params: 'a bmv_monad_param option list,
    Injs: term list list,
    Sbs: term list,
    Vrs: term option list list list,
    bd_infinite_regular_card_order: 'a,
    tacs: 'a bmv_monad_axioms list
  }

  val ops_of_bmv_monad: bmv_monad -> typ list;
  val bd_of_bmv_monad: bmv_monad -> term;
  val bd_infinite_regular_card_order_of_bmv_monad: bmv_monad -> thm;
  val var_class_of_bmv_monad: bmv_monad -> class;
  val leader_of_bmv_monad: bmv_monad -> int;
  val frees_of_bmv_monad: bmv_monad -> typ list;
  val lives_of_bmv_monad: bmv_monad -> typ list;
  val lives'_of_bmv_monad: bmv_monad -> typ list;
  val Injs_of_bmv_monad: bmv_monad -> term list list;
  val Sbs_of_bmv_monad: bmv_monad -> term list;
  val Maps_of_bmv_monad: bmv_monad -> term option list;
  val Supps_of_bmv_monad: bmv_monad -> term list option list;
  val Vrs_of_bmv_monad: bmv_monad -> term option list list list;
  val axioms_of_bmv_monad: bmv_monad -> thm bmv_monad_axioms list;
  val params_of_bmv_monad: bmv_monad -> {
    Map: term,
    Supps: term list,
    axioms: thm supported_functor_axioms,
    Map_Sb: thm,
    Supp_Sb: thm list,
    Map_Vrs: thm option list list
  } option list;

  val map_bmv_monad_axioms: ('a -> 'b) -> 'a bmv_monad_axioms -> 'b bmv_monad_axioms;
  val apply_bmv_monad_axioms: ('a -> 'b) bmv_monad_axioms -> 'a bmv_monad_axioms -> 'b bmv_monad_axioms;
  val morph_bmv_monad: morphism -> bmv_monad -> bmv_monad;

  val register_pbmv_monad: string -> bmv_monad -> local_theory -> local_theory;
  val pbmv_monad_of_generic: Context.generic -> string -> bmv_monad option;
  val pbmv_monad_of: Proof.context -> string -> bmv_monad option;

  val pbmv_monad_of_bnf: BNF_Def.bnf -> local_theory -> bmv_monad * local_theory
  val register_bnf_as_pbmv_monad: string -> local_theory -> local_theory
  val bmv_monad_def: BNF_Def.inline_policy -> (Proof.context -> BNF_Def.fact_policy)
    -> (binding -> binding) -> (Proof.context -> tactic) bmv_monad_model -> local_theory -> (bmv_monad * thm list) * local_theory

  val compose_bmv_monad: (binding -> binding) -> bmv_monad -> (bmv_monad, typ) MRBNF_Util.either list -> local_theory
    -> (bmv_monad * thm list) * local_theory
end

structure BMV_Monad_Def : BMV_MONAD_DEF = struct

open MRBNF_Util

type 'a bmv_monad_axioms = {
  Sb_Inj: 'a,
  Sb_comp_Injs: 'a list,
  Sb_comp: 'a,
  Sb_cong: 'a,
  Vrs_bds: 'a option list list,
  Vrs_Injs: 'a option list list,
  Vrs_Sbs: 'a option list list
};

fun map_bmv_monad_axioms f ({
  Sb_Inj, Sb_comp_Injs, Sb_comp, Sb_cong, Vrs_bds, Vrs_Injs, Vrs_Sbs
}: 'a bmv_monad_axioms) = {
  Sb_Inj = f Sb_Inj,
  Sb_comp_Injs = map f Sb_comp_Injs,
  Sb_comp = f Sb_comp,
  Sb_cong = f Sb_cong,
  Vrs_bds = map (map (Option.map f)) Vrs_bds,
  Vrs_Injs = map (map (Option.map f)) Vrs_Injs,
  Vrs_Sbs = map (map (Option.map f)) Vrs_Sbs
} : 'b bmv_monad_axioms;

val morph_bmv_monad_axioms = map_bmv_monad_axioms o Morphism.thm;

fun apply_bmv_monad_axioms ({
  Sb_Inj=f1, Sb_comp_Injs=f2s, Sb_comp=f3, Sb_cong=f4, Vrs_bds=f5s, Vrs_Injs=f6s, Vrs_Sbs=f7s
}: ('a -> 'b) bmv_monad_axioms) ({
  Sb_Inj, Sb_comp_Injs, Sb_comp, Sb_cong, Vrs_bds, Vrs_Injs, Vrs_Sbs
}: 'a bmv_monad_axioms) = {
  Sb_Inj = f1 Sb_Inj,
  Sb_comp_Injs = map2 (curry (op|>)) Sb_comp_Injs f2s,
  Sb_comp = f3 Sb_comp,
  Sb_cong = f4 Sb_cong,
  Vrs_bds = map2 (map2 (@{map_option 2} (curry (op|>)))) Vrs_bds f5s,
  Vrs_Injs = map2 (map2 (@{map_option 2} (curry (op|>)))) Vrs_Injs f6s,
  Vrs_Sbs = map2 (map2 (@{map_option 2} (curry (op|>)))) Vrs_Sbs f7s
} : 'b bmv_monad_axioms;

type 'a supported_functor_axioms = {
  Map_id: 'a,
  Map_comp: 'a,
  Supp_Map: 'a list,
  Supp_bd: 'a list,
  Map_cong: 'a
};

fun map_supported_functor_axioms f { Map_id, Map_comp, Supp_Map, Supp_bd, Map_cong } = {
  Map_id = f Map_id,
  Map_comp = f Map_comp,
  Supp_Map = map f Supp_Map,
  Supp_bd = map f Supp_bd,
  Map_cong = f Map_cong
} : 'b supported_functor_axioms;

type 'a bmv_monad_param = {
  Map: term,
  Supps: term list,
  axioms: 'a supported_functor_axioms,
  Map_Sb: 'a,
  Supp_Sb: 'a list,
  Map_Vrs: 'a option list list
};

fun morph_bmv_monad_param phi f ({ Map, Supps, axioms, Map_Sb, Supp_Sb, Map_Vrs }: 'a bmv_monad_param) = {
  Map = Morphism.term phi Map,
  Supps = map (Morphism.term phi) Supps,
  axioms = map_supported_functor_axioms f axioms,
  Map_Sb = f Map_Sb,
  Supp_Sb = map f Supp_Sb,
  Map_Vrs = map (map (Option.map f)) Map_Vrs
}: 'b bmv_monad_param;

datatype bmv_monad = BMV of {
  ops: typ list,
  bd: term,
  var_class: class,
  leader: int,
  frees: typ list,
  lives: typ list,
  lives': typ list,
  params: thm bmv_monad_param option list,
  Injs: term list list,
  Sbs: term list,
  Vrs: term option list list list,
  bd_infinite_regular_card_order: thm,
  axioms: thm bmv_monad_axioms list
}

fun morph_bmv_monad phi (BMV {
  ops, bd, var_class, leader, frees, lives, lives', params, Injs, Sbs, Vrs, axioms,
  bd_infinite_regular_card_order
}) = BMV {
  ops = map (Morphism.typ phi) ops,
  bd = Morphism.term phi bd,
  leader = leader,
  var_class = var_class,
  frees = map (Morphism.typ phi) frees,
  lives = map (Morphism.typ phi) lives,
  lives' = map (Morphism.typ phi) lives',
  params = map (Option.map (morph_bmv_monad_param phi (Morphism.thm phi))) params,
  Injs = map (map (Morphism.term phi)) Injs,
  Sbs = map (Morphism.term phi) Sbs,
  Vrs = map (map (map (Option.map (Morphism.term phi)))) Vrs,
  axioms = map (morph_bmv_monad_axioms phi) axioms,
  bd_infinite_regular_card_order = Morphism.thm phi bd_infinite_regular_card_order
}

fun Rep_bmv (BMV x) = x

val ops_of_bmv_monad = #ops o Rep_bmv
val bd_of_bmv_monad = #bd o Rep_bmv
val var_class_of_bmv_monad = #var_class o Rep_bmv;
val leader_of_bmv_monad = #leader o Rep_bmv
val frees_of_bmv_monad = #frees o Rep_bmv
val lives_of_bmv_monad = #lives o Rep_bmv
val lives'_of_bmv_monad = #lives' o Rep_bmv
val Injs_of_bmv_monad = #Injs o Rep_bmv
val Sbs_of_bmv_monad = #Sbs o Rep_bmv
val Maps_of_bmv_monad = map (Option.map #Map) o #params o Rep_bmv
val Supps_of_bmv_monad = map (Option.map #Supps) o #params o Rep_bmv
val Vrs_of_bmv_monad = #Vrs o Rep_bmv
val axioms_of_bmv_monad = #axioms o Rep_bmv
val params_of_bmv_monad = #params o Rep_bmv
val bd_infinite_regular_card_order_of_bmv_monad = #bd_infinite_regular_card_order o Rep_bmv

type 'a bmv_monad_model = {
  ops: typ list,
  bd: term,
  var_class: class,
  frees: typ list,
  lives: typ list,
  lives': typ list,
  params: 'a bmv_monad_param option list,
  bmv_ops: bmv_monad list,
  leader: int,
  Injs: term list list,
  Sbs: term list,
  Vrs: term option list list list,
  bd_infinite_regular_card_order: 'a,
  tacs: 'a bmv_monad_axioms list
}

fun morph_bmv_monad_model phi f ({ ops, bd, var_class, frees, lives, lives', params, bmv_ops, leader,
  Injs, Sbs, Vrs, tacs, bd_infinite_regular_card_order }
) = {
  ops = map (Morphism.typ phi) ops,
  bd = Morphism.term phi bd,
  var_class = var_class,
  frees = map (Morphism.typ phi) frees,
  lives = map (Morphism.typ phi) lives,
  lives' = map (Morphism.typ phi) lives',
  params = map (Option.map (morph_bmv_monad_param phi f)) params,
  bmv_ops = map (morph_bmv_monad phi) bmv_ops,
  leader = leader,
  Injs = map (map (Morphism.term phi)) Injs,
  Sbs = map (Morphism.term phi) Sbs,
  Vrs = map (map (map (Option.map (Morphism.term phi)))) Vrs,
  tacs = map (map_bmv_monad_axioms f) tacs,
  bd_infinite_regular_card_order = bd_infinite_regular_card_order
} : 'b bmv_monad_model;

structure Data = Generic_Data (
  type T = bmv_monad Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
);

fun register_pbmv_monad name bmv =
  Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
    (fn phi => Data.map (Symtab.update (name, morph_bmv_monad phi bmv)));

fun pbmv_monad_of_generic context =
  Option.map (morph_bmv_monad (Morphism.transfer_morphism (Context.theory_of context)))
  o Symtab.lookup (Data.get context);

val pbmv_monad_of = pbmv_monad_of_generic o Context.Proof;

val mk_small_prems = map2 (fn rho => fn Inj => HOLogic.mk_Trueprop (mk_ordLess
  (mk_card_of (HOLogic.mk_Collect ("a", fst (dest_funT (fastype_of Inj)),
    HOLogic.mk_not (HOLogic.mk_eq (rho $ Bound 0, Inj $ Bound 0))
  )))
  (mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of Inj)))))
));

fun mk_bmv_monad_axioms ops bd Sb Injs Vrs bmv_ops lthy =
  let
    val Ts = ops @ maps ops_of_bmv_monad bmv_ops;
    val Sbs = Sb @ maps Sbs_of_bmv_monad bmv_ops;
    val Injss = Injs @ maps Injs_of_bmv_monad bmv_ops;
    val Vrss = Vrs @ maps Vrs_of_bmv_monad bmv_ops;

    val axioms = @{map 4} (fn T => fn Injs => fn Sb => fn Vrs =>
      let
        val (own_Injs, other_Injs) = partition (fn Inj => member (op=) ops (body_type (fastype_of Inj))) Injs;
        val is_own_Inj = map (member (op=) ops o body_type o fastype_of) Injs;
        val other_idxs = map (fn Inj => find_index (fn T => body_type (fastype_of Inj) = T) Ts) other_Injs;
        val ((((rhos, rhos'), aa), x), _) = lthy
          |> mk_Frees "\<rho>" (map fastype_of Injs)
          ||>> mk_Frees "\<rho>'" (map fastype_of Injs)
          ||>> mk_Frees "a" (map (fst o dest_funT o fastype_of) Injs)
          ||>> apfst hd o mk_Frees "x" [T];
        val nown = length own_Injs;
        val (own_rhos, other_rhos) = chop nown rhos;

        val Sb_Inj = mk_Trueprop_eq (Term.list_comb (Sb, Injs), HOLogic.id_const T);

        val small_prems = mk_small_prems rhos Injs;
        val small_prems' = mk_small_prems rhos' Injs;

        val Sb_comp_Injs = map2 (fn Inj => fn rho =>
          fold_rev Logic.all rhos (fold_rev (curry Logic.mk_implies) small_prems (mk_Trueprop_eq (
            HOLogic.mk_comp (Term.list_comb (Sb, rhos), Inj), rho
          )))
        ) own_Injs own_rhos;

        val Sb_comp = fold_rev Logic.all (rhos' @ rhos) (
          fold_rev (curry Logic.mk_implies) (small_prems @ small_prems') (mk_Trueprop_eq (
            HOLogic.mk_comp (Term.list_comb (Sb, rhos'), Term.list_comb (Sb, rhos)),
            Term.list_comb (Sb, map (fn rho => HOLogic.mk_comp (
              Term.list_comb (Sb, rhos'), rho
            )) own_rhos @ @{map 3} (fn rho => fn Sb => fn Injs =>
              HOLogic.mk_comp (Term.list_comb (Sb, map (fn Inj =>
                case List.find (fn rho' => fastype_of rho' = fastype_of Inj) rhos' of
                  NONE => Inj | SOME t => t
              ) Injs), rho)
            ) other_rhos (map (nth Sbs) other_idxs) (map (nth Injss) other_idxs))
          ))
        );

        val Vrs_bds = map (map (Option.map (fn Vrs => Logic.all x (
          HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (Vrs $ x)) bd)
        )))) Vrs;

        val Vrs_Injs = map2 (fn Inj => map (Option.map (fn Vrs =>
          let
            val a = the (List.find (fn a => fastype_of a = hd (binder_types (fastype_of Inj))) aa);
            val T = HOLogic.dest_setT (body_type (fastype_of Vrs));
          in Logic.all a (mk_Trueprop_eq (
            Vrs $ (Inj $ a),
            if fastype_of a = T then mk_singleton a else mk_bot T))
          end))) own_Injs (cond_keep Vrs is_own_Inj);

        val Vrs_Sbs = map2 (fn rho => map (Option.map (fn Vrs =>
          let
            val var = HOLogic.dest_setT (body_type (fastype_of Vrs));
            val idx = find_index (fn T => body_type (fastype_of rho) = T) Ts;
            val idx' = find_index (fn t => fastype_of t = fastype_of rho) (nth Injss idx);
            val Vrs' = hd (map_filter (Option.mapPartial (fn t =>
              if HOLogic.dest_setT (body_type (fastype_of t)) = var then SOME t else NONE
            )) (nth (nth Vrss idx) idx'));
          in fold_rev Logic.all (rhos @ [x]) (
            fold_rev (curry Logic.mk_implies) small_prems (mk_Trueprop_eq (
              Vrs $ (Term.list_comb (Sb, rhos) $ x),
              mk_UNION (Vrs $ x) (Term.abs ("a", var) (Vrs' $ (rho $ Bound 0)))
            ))
          ) end
        ))) rhos Vrs;

        val Sb_cong = fold_rev Logic.all (rhos @ rhos' @ [x]) (
          fold_rev (curry Logic.mk_implies) (small_prems @ small_prems' @ flat (@{map 3} (fn rho => fn rho' => map_filter (Option.map (fn Vrs =>
            let val a = the (List.find (fn t => fastype_of t = HOLogic.dest_setT (body_type (fastype_of Vrs))) aa)
            in Logic.all a (Logic.mk_implies (
              HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Vrs $ x)),
              mk_Trueprop_eq (rho $ a, rho' $ a)
            )) end
          ))) rhos rhos' Vrs)) (mk_Trueprop_eq (
            Term.list_comb (Sb, rhos) $ x,
            Term.list_comb (Sb, rhos') $ x
          )
        ));

      in {
        Sb_Inj = Sb_Inj,
        Sb_comp_Injs = Sb_comp_Injs,
        Sb_comp = Sb_comp,
        Vrs_Injs = Vrs_Injs,
        Vrs_bds = Vrs_bds,
        Vrs_Sbs = Vrs_Sbs,
        Sb_cong = Sb_cong
      } : term bmv_monad_axioms end
    ) ops Injs Sb Vrs;
  in axioms end;

fun mk_param_axioms (model: 'a bmv_monad_model) lthy = @{map 5} (fn T => fn Sb => fn Injs => fn Vrs => Option.map (fn param =>
  let
    val (Cs, _) = lthy
      |> mk_TFrees (length (#lives model));
    val ((((fs, gs), rhos), x), _) = lthy
      |> mk_Frees "f" (map2 (curry (op-->)) (#lives model) (#lives' model))
      ||>> mk_Frees "g" (map2 (curry (op-->)) (#lives' model) Cs)
      ||>> mk_Frees "\<rho>" (map fastype_of Injs)
      ||>> apfst hd o mk_Frees "x" [T];;

    val Map_id = Term.subst_atomic_types (#lives' model ~~ #lives model) (
      mk_Trueprop_eq (
        Term.list_comb (#Map param, map HOLogic.id_const (#lives model)), HOLogic.id_const T
      )
    );

    val Map_comp = fold_rev Logic.all (fs @ gs) (mk_Trueprop_eq (
      HOLogic.mk_comp (Term.list_comb (
        Term.subst_atomic_types ((#lives model @ #lives' model) ~~ (#lives' model @ Cs)) (#Map param), gs
      ), Term.list_comb (#Map param, fs)),
      Term.list_comb (Term.subst_atomic_types (#lives' model ~~ Cs) (#Map param), map2 (curry HOLogic.mk_comp) gs fs)
    ));

    val Supp_Maps = map2 (fn Supp => fn f =>
      fold_rev Logic.all (fs @ [x]) (mk_Trueprop_eq (
        Term.subst_atomic_types (#lives model ~~ #lives' model) Supp $ (Term.list_comb (#Map param, fs) $ x),
        mk_image f $ (Supp $ x)
      ))
    ) (#Supps param) fs;

    val Supp_bds = map (fn Supp => Logic.all x (HOLogic.mk_Trueprop (
      mk_ordLess (mk_card_of (Supp $ x)) (#bd model)
    ))) (#Supps param);

    val (gs', _) = lthy
      |> mk_Frees "g" (map fastype_of fs);
    val Map_cong = fold_rev Logic.all (fs @ gs' @ [x]) (
      fold_rev (curry Logic.mk_implies) (@{map 3} (fn Supp => fn f => fn g =>
        let val a = Free ("a", hd (binder_types (fastype_of f)));
        in Logic.all a (Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Supp $ x)),
          mk_Trueprop_eq (f $ a, g $ a)
        )) end
      ) (#Supps param) fs gs') (mk_Trueprop_eq (
        Term.list_comb (#Map param, fs) $ x,
        Term.list_comb (#Map param, gs') $ x
      )));

    val Map_Sb = fold_rev Logic.all (fs @ rhos) (
      fold_rev (curry Logic.mk_implies) (mk_small_prems rhos Injs) (mk_Trueprop_eq (
        HOLogic.mk_comp (Term.list_comb (#Map param, fs), Term.list_comb (Sb, rhos)),
        HOLogic.mk_comp (Term.list_comb (
          Term.subst_atomic_types (#lives model ~~ #lives' model) Sb, rhos
        ), Term.list_comb (#Map param, fs))
      ))
    );

    val Map_Vrs = map (map (Option.map (fn Vrs =>
      fold_rev Logic.all (fs @ [x]) (mk_Trueprop_eq (
        Term.subst_atomic_types (#lives model ~~ #lives' model) Vrs $ (Term.list_comb (#Map param, fs) $ x),
        Vrs $ x
      ))
    ))) Vrs;

    val Supp_Sb = map (fn Supp =>
      fold_rev Logic.all (rhos @ [x]) (mk_Trueprop_eq (
        Supp $ (Term.list_comb (Sb, rhos) $ x), Supp $ x
      ))
    ) (#Supps param);
  in {
    Map = #Map param,
    Supps = #Supps param,
    axioms = {
      Map_id = Map_id,
      Map_comp = Map_comp,
      Supp_Map = Supp_Maps,
      Supp_bd = Supp_bds,
      Map_cong = Map_cong
    } : term supported_functor_axioms,
    Map_Sb = Map_Sb,
    Supp_Sb = Supp_Sb,
    Map_Vrs = Map_Vrs
  }: term bmv_monad_param end
)) (#ops model) (#Sbs model) (#Injs model) (#Vrs model) (#params model);

val smart_max_inline_term_size = 25; (*FUDGE*)

fun maybe_define const_policy fact_policy b rhs lthy =
  let
    val inline = case const_policy of
      BNF_Def.Dont_Inline => false
      | BNF_Def.Hardly_Inline => Term.is_Free rhs orelse Term.is_Const rhs
      | BNF_Def.Smart_Inline => Term.size_of_term rhs <= smart_max_inline_term_size
      | BNF_Def.Do_Inline => true;
    val thm_b = Thm.def_binding b;
    (* TODO: difference between define_internal and define *)
    val (define, thm_b) = if fact_policy = BNF_Def.Dont_Note then
      (Local_Theory.define_internal, Binding.concealed thm_b)
    else (Local_Theory.define, thm_b)

  in if inline then
    ((rhs, NONE), lthy)
  else
    apfst (apsnd (SOME o snd)) (define ((b, NoSyn), ((thm_b, []), rhs)) lthy)
  end

fun fold_map_option _ NONE b = (NONE, b)
  | fold_map_option f (SOME x) b = apfst SOME (f x b)

fun define_bmv_monad_consts const_policy fact_policy qualify (model: 'a bmv_monad_model) lthy =
  let
    val maybe_define = maybe_define const_policy fact_policy o qualify;

    val suffixes = map_index (fn (i, T) => Binding.suffix_name ("_" ^ (case T of
      Type (n, Ts) => if forall Term.is_TFree Ts then short_type_name n else string_of_int i
      | _ => string_of_int i
    ))) (#ops model);
    val suffixess = map2 (fn suffix => map_index (fn (i, _) =>
      Binding.suffix_name ("_" ^ string_of_int i) o suffix
    )) suffixes (#Injs model);

    val (_, lthy) = Local_Theory.begin_nested lthy;
    val ((Sbs, Sb_defs), lthy) = apfst split_list (@{fold_map 2} (fn Sb => fn suffix =>
      maybe_define (suffix (Binding.name "Sb")) Sb
    ) (#Sbs model) suffixes lthy);

    val ((Injs, Inj_defs), lthy) = apfst (split_list o map split_list) (@{fold_map 2} (
      @{fold_map 2} (fn Inj => fn suffix => maybe_define (suffix (Binding.name "Inj")) Inj)
    ) (#Injs model) suffixess lthy);

    val (Vrs', lthy) =
      (@{fold_map 2} (@{fold_map 2} (fn suffix => fn Vrs => @{fold_map 2} (fn i => fold_map_option (fn Vrs =>
        maybe_define (Binding.suffix_name ("_" ^ string_of_int i) (suffix (Binding.name "Vrs"))) Vrs
      )) (0 upto length Vrs - 1) Vrs)) suffixess (#Vrs model) lthy);

    val Vrs = map (map (map (Option.map fst))) Vrs';
    val Vrs_defs = maps (maps (map (Option.mapPartial snd))) Vrs';

    val (params', lthy) = @{fold_map 2} (fn suffix => fold_map_option (fn param => fn lthy =>
      let
        val ((Map, Map_def), lthy) = maybe_define (suffix (Binding.name "Map")) (#Map param) lthy;
        val ((Supps, Supp_defs), lthy) = apfst split_list (@{fold_map 2} (fn i =>
          maybe_define (Binding.suffix_name ("_" ^ string_of_int i) (suffix (Binding.name "Supp")))
        ) (0 upto length (#Supps param) - 1) (#Supps param) lthy);
        val param = {
          Map = Map,
          Supps = Supps,
          axioms = #axioms param,
          Map_Sb = #Map_Sb param,
          Supp_Sb = #Supp_Sb param,
          Map_Vrs = #Map_Vrs param
        }: 'a bmv_monad_param;
      in ((param, Map_def :: Supp_defs), lthy) end
    )) suffixes (#params model) lthy;
    val params = map (Option.map fst) params';
    val param_defs = map_filter (Option.map snd) params';

    val ((bd, bd_def), lthy) = maybe_define (Binding.name "bd") (#bd model) lthy;

    val model' = {
      ops = #ops model,
      bd = bd,
      var_class = #var_class model,
      leader = #leader model,
      frees = #frees model,
      lives = #lives model,
      lives' = #lives' model,
      bmv_ops = #bmv_ops model,
      params = params,
      Injs = Injs,
      Sbs = Sbs,
      Vrs = Vrs,
      bd_infinite_regular_card_order = #bd_infinite_regular_card_order model,
      tacs = #tacs model
    } : 'a bmv_monad_model;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val vars = map TFree (rev (Term.add_tfreesT (nth (#ops model) (#leader model)) [])) @ #lives' model;
    val subst = (map (Morphism.typ phi) vars ~~ vars);

    val phi' = Morphism.term_morphism "bmv_monad_export" (Term.subst_atomic_types subst o Morphism.term phi)
    val model' = morph_bmv_monad_model phi' I model';

    val defs = map_filter I (Sb_defs @ flat Inj_defs @ Vrs_defs @ [bd_def] @ flat param_defs);
  in (model', map (Morphism.thm phi) defs, lthy) end;

fun mk_bmv_monad const_policy fact_policy (model: thm bmv_monad_model) lthy =
  let
    (* TODO: Derived theorems *)

    val bmv = BMV {
      ops = #ops model @ maps (#ops o Rep_bmv) (#bmv_ops model),
      bd = #bd model,
      var_class = #var_class model,
      leader = #leader model,
      frees = #frees model,
      lives = #lives model,
      lives' = #lives' model,
      params = #params model @ maps (#params o Rep_bmv) (#bmv_ops model),
      Injs = #Injs model @ maps (#Injs o Rep_bmv) (#bmv_ops model),
      Sbs = #Sbs model @ maps (#Sbs o Rep_bmv) (#bmv_ops model),
      Vrs = #Vrs model @ maps (#Vrs o Rep_bmv) (#bmv_ops model),
      axioms = #tacs model @ maps (#axioms o Rep_bmv) (#bmv_ops model),
      bd_infinite_regular_card_order = #bd_infinite_regular_card_order model
    } : bmv_monad;
  in (bmv, lthy) end

fun prove_axioms (model: (Proof.context -> tactic) bmv_monad_model) defs lthy =
  let
    val goals = mk_bmv_monad_axioms (#ops model) (#bd model) (#Sbs model) (#Injs model) (#Vrs model) (#bmv_ops model) lthy;
    val tacs' = map (map_bmv_monad_axioms (fn tac => fn ctxt => Local_Defs.unfold0_tac ctxt defs THEN tac ctxt)) (#tacs model);
  in map2 apply_bmv_monad_axioms
    (map (map_bmv_monad_axioms (fn goal => fn tac => Goal.prove_sorry lthy [] [] goal (tac o #context))) goals)
    tacs'
  end;

fun prove_params (model: (Proof.context -> tactic) bmv_monad_model) defs lthy =
  let
    val goals = mk_param_axioms model lthy;
    val tacs' = map (Option.map (morph_bmv_monad_param Morphism.identity (fn tac => fn goal =>
      Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, ...} =>
       Local_Defs.unfold0_tac ctxt defs THEN tac ctxt
     )
    ))) (#params model);
  in map2 (@{map_option 2} (
    fn { axioms=tacs, Map_Sb=f1, Supp_Sb=f2s, Map_Vrs=f3s, ...} =>
    fn { Map, Supps, axioms, Map_Sb, Supp_Sb, Map_Vrs } => {
      Map = Map, Supps = Supps, Map_Sb = f1 Map_Sb, Supp_Sb = map2 (curry (op|>)) Supp_Sb f2s,
      Map_Vrs = map2 (map2 (@{map_option 2} (curry (op|>)))) Map_Vrs f3s, axioms = {
        Map_id = #Map_id tacs (#Map_id axioms),
        Map_comp = #Map_comp tacs (#Map_comp axioms),
        Supp_Map = map2 (curry (op|>)) (#Supp_Map axioms) (#Supp_Map tacs),
        Supp_bd = map2 (curry (op|>)) (#Supp_bd axioms) (#Supp_bd tacs),
        Map_cong = #Map_cong tacs (#Map_cong axioms)
      }
  } : thm bmv_monad_param)) tacs' goals end;

fun mk_thm_model (model: 'a bmv_monad_model) params axioms bd_irco = {
  ops = #ops model,
  bd = #bd model,
  var_class = #var_class model,
  leader = #leader model,
  frees = #frees model,
  lives = #lives model,
  lives' = #lives' model,
  bmv_ops = #bmv_ops model,
  params = params,
  Injs = #Injs model,
  Sbs = #Sbs model,
  Vrs = #Vrs model,
  bd_infinite_regular_card_order = bd_irco,
  tacs = axioms
} : thm bmv_monad_model;

fun bmv_monad_def const_policy fact_policy qualify (model: (Proof.context -> tactic) bmv_monad_model) lthy =
  let
    val frees = map (fn T => TFree (apsnd (
      Sign.minimize_sort (Proof_Context.theory_of lthy) o cons (#var_class model)
    ) (dest_TFree T))) (#frees model);
    val model = morph_bmv_monad_model (MRBNF_Util.subst_typ_morphism (#frees model ~~ frees)) I model;

    val (model, unfold_set, lthy) = define_bmv_monad_consts const_policy (fact_policy lthy) qualify model lthy;

    val axioms = prove_axioms model unfold_set lthy;
    val params = prove_params model unfold_set lthy;

    val bd_irco = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (
      mk_infinite_regular_card_order (#bd model)
    )) (fn {context=ctxt, ...} => Local_Defs.unfold0_tac ctxt unfold_set THEN #bd_infinite_regular_card_order model ctxt);

    val model = mk_thm_model model params axioms bd_irco;
  in apfst (rpair unfold_set) (mk_bmv_monad const_policy fact_policy model lthy) end

fun pbmv_monad_of_bnf bnf lthy =
  let
    val (((lives, lives'), deads), _) = lthy
      |> mk_TFrees (BNF_Def.live_of_bnf bnf)
      ||>> mk_TFrees (BNF_Def.live_of_bnf bnf)
      ||>> mk_TFrees' (map Type.sort_of_atyp (BNF_Def.deads_of_bnf bnf))
    val T = BNF_Def.mk_T_of_bnf deads lives bnf;
    val n = BNF_Def.live_of_bnf bnf;
    val var_class = case BNF_Def.bd_of_bnf bnf of
      @{term natLeq} => @{class var}
      | _ => error "TODO: other var classes"
   in apfst fst (bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Dont_Note) I {
     ops = [T],
     bd = BNF_Def.bd_of_bnf bnf,
     var_class = var_class,
     leader = 0,
     frees = [],
     lives = lives,
     lives' = lives',
     bmv_ops = [],
     params = [SOME {
       Map = BNF_Def.mk_map_of_bnf deads lives lives' bnf,
       Supps = BNF_Def.mk_sets_of_bnf (replicate n deads) (replicate n lives) bnf,
       axioms = {
         Map_id = fn ctxt => rtac ctxt (BNF_Def.map_id0_of_bnf bnf) 1,
         Map_comp = fn ctxt => rtac ctxt (BNF_Def.map_comp0_of_bnf bnf RS sym) 1,
         Supp_Map = map (fn thm => fn ctxt => rtac ctxt thm 1) (BNF_Def.set_map_of_bnf bnf),
         Supp_bd = map (fn thm => fn ctxt => rtac ctxt thm 1) (BNF_Def.set_bd_of_bnf bnf),
         Map_cong = fn ctxt => EVERY1 [
           rtac ctxt (BNF_Def.map_cong0_of_bnf bnf),
           REPEAT_DETERM o Goal.assume_rule_tac ctxt
         ]
       },
       Map_Sb = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms id_o o_id} THEN rtac ctxt refl 1,
       Supp_Sb = replicate n (fn ctxt => Local_Defs.unfold0_tac ctxt @{thms id_apply} THEN rtac ctxt refl 1),
       Map_Vrs = []
     }],
     Injs = [[]],
     Sbs = [HOLogic.id_const T],
     Vrs = [[]],
     bd_infinite_regular_card_order = fn ctxt => EVERY1 [
       rtac ctxt @{thm infinite_regular_card_order.intro},
       rtac ctxt (BNF_Def.bd_card_order_of_bnf bnf),
       rtac ctxt (BNF_Def.bd_cinfinite_of_bnf bnf),
       rtac ctxt (BNF_Def.bd_regularCard_of_bnf bnf)
     ],
     tacs = [{
       Sb_Inj = fn ctxt => rtac ctxt refl 1,
       Sb_comp_Injs = [],
       Sb_comp = fn ctxt => rtac ctxt @{thm id_o} 1,
       Vrs_bds = [],
       Vrs_Injs = [],
       Vrs_Sbs = [],
       Sb_cong = fn ctxt => rtac ctxt refl 1
     }]
   } lthy) end;

fun register_bnf_as_pbmv_monad name lthy =
  let
    val bnf = the (BNF_Def.bnf_of lthy name);
    val (bmv, lthy) = pbmv_monad_of_bnf bnf lthy;
    val lthy = register_pbmv_monad name bmv lthy;
  in lthy end

(* Cleanup: Throw away op iff any:
- not the leader
- does not appear in the codomain of any (=of any **other** SOp) Injection,
*)

fun compose_bmv_monad qualify (outer : bmv_monad) (inners : (bmv_monad, typ) either list) lthy =
  let
    val _ = if length (lives_of_bmv_monad outer) <> length inners then
      error "Outer needs exactly as many lives as there are inners" else ()

    val filter_bmvs = map_filter (fn Inl x => SOME x | _ => NONE);

    val frees = fold (fn a =>
      let val (n, s) = dest_TFree a
      in Symtab.map_default (n, s) (curry (Sign.inter_sort (Proof_Context.theory_of lthy)) s) end
    ) (frees_of_bmv_monad outer @ maps frees_of_bmv_monad (filter_bmvs inners)) Symtab.empty;

    fun mk_sign_morph bmv =
      morph_bmv_monad (MRBNF_Util.subst_typ_morphism (map (fn a =>
        let val (n, _) = dest_TFree a;
        in (a, TFree (n, the (Symtab.lookup frees n))) end
      ) (frees_of_bmv_monad bmv))) bmv;
    fun mk_T_morph T =
      let val vars = Term.add_tfreesT T [];
      in Term.typ_subst_atomic (map (fn x =>
        (TFree x, the_default (TFree x) (Option.map (TFree o pair (fst x)) (Symtab.lookup frees (fst x))))
      ) vars) T end
    val outer = mk_sign_morph outer;
    val inners = map (map_sum mk_sign_morph mk_T_morph) inners;

    val bmvs = Typtab.make_distinct (flat (map (fn bmv => (#ops bmv ~~
      ((#params bmv) ~~ (#Injs bmv) ~~ (#Sbs bmv) ~~ (#Vrs bmv) ~~ map SOME (#axioms bmv) ~~ replicate (length (#Sbs bmv)) (SOME bmv))
    )) (map_filter (fn Inl bmv => SOME (Rep_bmv bmv) | Inr _ => NONE) inners)));

    val outer_ops' = map (fn T => if Typtab.defined bmvs T then NONE else SOME T) (
      map (Term.typ_subst_atomic (lives_of_bmv_monad outer ~~ map (
        fn Inl bmv => nth (ops_of_bmv_monad bmv) (leader_of_bmv_monad bmv)
          | Inr T => T
      ) inners)) (ops_of_bmv_monad outer)
    );

    val ((Sbs, Injs), Vrs) = apfst split_list (split_list (@{map 5} (fn NONE => K (K (K (K ((NONE, NONE), NONE)))) | SOME T => (fn NONE => K (K (K ((NONE, NONE), NONE)))
      | SOME param => fn Sb => fn Injs => fn Vrs =>
      let
        val ((Sbs, Ts), (Injss, Vrsss)) = apfst split_list (apsnd split_list (split_list (map (fn Inl bmv =>
          let fun pick xs = nth xs (leader_of_bmv_monad bmv)
          in (
            (SOME (pick (Sbs_of_bmv_monad bmv)), pick (ops_of_bmv_monad bmv)),
            (SOME (pick (Injs_of_bmv_monad bmv)), SOME (pick (Vrs_of_bmv_monad bmv)))
          ) end
          | Inr T => ((NONE, T), (NONE, NONE))
        ) inners)));
        val subst = (lives_of_bmv_monad outer @ lives'_of_bmv_monad outer) ~~ (Ts @ Ts);
        val Injs' = distinct ((op=) o apply2 fastype_of) (Injs @ flat (map_filter I Injss));
        val ((fs, x), _) = lthy
          |> mk_Frees "f" (map fastype_of Injs')
          ||>> apfst hd o mk_Frees "x" [T];

        val Vrs' = @{fold 4} (fn i => fn inner => fn Injs => fn Vrss => fn tab => case inner of
          Inr _ => tab
          | Inl inner => @{fold 2} (fn Inj => fn Vrs => fn tab =>
            case Typtab.lookup tab (fastype_of Inj) of
              NONE => tab
              | SOME inner_tab =>
                let val inner_tab' = @{fold 2} (fn NONE => K I | SOME Vrs => fn free =>
                  Typtab.map_default (free, [(i, Vrs)]) (cons (i, Vrs))
                ) Vrs (frees_of_bmv_monad inner) inner_tab;
                in Typtab.update (fastype_of Inj, inner_tab') tab end
          ) (the Injs) (the Vrss) tab
        ) (0 upto length inners) (Inl outer :: inners) (SOME Injs :: Injss) (SOME Vrs :: Vrsss) (Typtab.make (map (rpair Typtab.empty o fastype_of) Injs'));

        val frees = distinct (op=) (maps snd (Typtab.dest (Typtab.map (K Typtab.keys) Vrs')));
        val Supps = map (Term.subst_atomic_types subst) (#Supps param);

        val Vrs' = map (fn Inj => map (fn free => Option.mapPartial (fn xs =>
          let
            val Vrss = distinct (op=) (rev xs);
            val Vrs' = the_default [] (Option.map (fn s =>
              [Term.subst_atomic_types subst (s $ x)]
            ) (AList.lookup (op=) Vrss 0))
              @ @{map_filter 2} (fn i => fn Supp => Option.map (fn t =>
                mk_UNION (Supp $ x) t
              ) (AList.lookup (op=) Vrss i)) (1 upto length Supps) Supps;

          in case Vrs' of
            [] => NONE
            | _ => SOME (Term.absfree (dest_Free x) (foldl1 mk_Un Vrs'))
          end
        ) (Typtab.lookup (the (Typtab.lookup Vrs' (fastype_of Inj))) free)) frees) Injs';

        val find_fs = map (fn Inj =>
          the (List.find (fn f => fastype_of f = fastype_of Inj) fs)
        );
        fun mk_comp t = if true orelse length (binder_types (fastype_of Sb)) > 1 then
            HOLogic.mk_comp (t, Term.list_comb (Sb, find_fs Injs))
          else t
      in ((
        SOME (Term.subst_atomic_types subst (
          fold_rev (Term.absfree o dest_Free) fs (mk_comp (
            Term.list_comb (#Map param, @{map 3} (fn Inr T => K (K (HOLogic.id_const T))
              | _ => fn Sb => fn Injs => Term.list_comb (the Sb, find_fs (the Injs))
            ) inners Sbs Injss)
          ))
        )),
        SOME Injs'),
        SOME Vrs'
      ) end
    )) outer_ops' (#params (Rep_bmv outer)) (Sbs_of_bmv_monad outer) (Injs_of_bmv_monad outer) (Vrs_of_bmv_monad outer)));

    fun drop_lead xs = map_filter I (nth_drop (leader_of_bmv_monad outer) xs);

    val bmvs = @{fold 3} (fn T => fn Sb => fn Injs => Typtab.map_default (T,
      (((((NONE, Injs), Sb), []), NONE), NONE)
    ) I) (drop_lead outer_ops') (drop_lead Sbs) (drop_lead Injs) bmvs;

    fun add_ops T Injs bmvs = T :: flat (map_filter I (fst (fold_map (fn Inj => fn bmvs =>
      let val T = body_type (fastype_of Inj);
      in case Typtab.lookup bmvs T of
        NONE => (NONE, bmvs)
        | SOME (((((_, Injs), _), _), _), _) =>
          let val bmvs' = Typtab.delete T bmvs
          in (SOME (add_ops T Injs bmvs'), bmvs') end
      end
    ) Injs bmvs)));

    fun pick xs = nth xs (leader_of_bmv_monad outer)
    val ops = add_ops (the (pick outer_ops')) (the (pick Injs)) bmvs;

    val bmv_ops = map_filter (fn T => case Typtab.lookup bmvs T of
      SOME (((((param, Injs), Sb), Vrs), SOME axioms), SOME bmv) => SOME (BMV {
        ops = [T],
        bd = #bd bmv,
        var_class = #var_class bmv,
        leader = 0,
        frees = #frees bmv,
        lives = #lives bmv,
        lives' = #lives' bmv,
        params = [param],
        Injs = [Injs],
        Sbs = [Sb],
        Vrs = [Vrs],
        axioms = [axioms],
        bd_infinite_regular_card_order = #bd_infinite_regular_card_order bmv
      }) | _ => NONE
    ) ops;

    val ops' = subtract (fn (bmv, T) => hd (ops_of_bmv_monad bmv) = T) bmv_ops ops;

    val inners' = filter_bmvs inners;

    val idxs = map (fn T => find_index (curry (op=) T) ops) ops';
    val Vrs = map (the o nth Vrs) idxs;
    val Injs = map (the o nth Injs) idxs;
    val frees = distinct (op=) (maps frees_of_bmv_monad (outer :: inners'));
    val outer_Vrs = map (nth (Vrs_of_bmv_monad outer)) idxs;

    val model = {
      ops = ops',
      bmv_ops = bmv_ops,
      bd = bd_of_bmv_monad outer, (* TODO: compose bounds *)
      bd_infinite_regular_card_order = fn ctxt => rtac ctxt (bd_infinite_regular_card_order_of_bmv_monad outer) 1,
      var_class = var_class_of_bmv_monad outer,
      frees = frees,
      lives = distinct (op=) (maps lives_of_bmv_monad inners'),
      lives' = distinct (op=) (maps lives'_of_bmv_monad inners'),
      params = replicate (length ops') NONE,
      leader = 0,
      Injs = Injs,
      Sbs = map (the o nth Sbs) idxs,
      Vrs = Vrs,
      tacs = @{map 5} (fn axioms => fn param => fn Injs => fn Vrs => fn outer_Vrs => {
        Sb_Inj = fn ctxt => EVERY1 [
          rtac ctxt trans,
          rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
          rtac ctxt ext,
          rtac ctxt (trans OF [#Map_cong (#axioms param), #Map_id (#axioms param) RS fun_cong]),
          REPEAT_DETERM o resolve_tac ctxt (refl :: maps (map (fn ax =>
            #Sb_Inj ax RS fun_cong
          ) o axioms_of_bmv_monad) inners'),
          rtac ctxt @{thm trans[OF id_o]},
          rtac ctxt (#Sb_Inj axioms)
        ],
        Sb_comp_Injs = map (fn thm => fn ctxt =>
          print_tac ctxt "Sb_comp_Inj"
        ) (#Sb_comp_Injs axioms),
        Sb_comp = fn ctxt => EVERY1 [
          rtac ctxt @{thm trans[OF comp_assoc]},
          rtac ctxt trans,
          rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
          rtac ctxt @{thm trans[OF comp_assoc[symmetric]]},
          rtac ctxt trans,
          rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
          rtac ctxt (#Map_Sb param RS sym),
          REPEAT_DETERM o assume_tac ctxt,
          rtac ctxt @{thm trans[OF comp_assoc]},
          rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
          rtac ctxt (#Sb_comp axioms),
          REPEAT_DETERM o assume_tac ctxt,
          rtac ctxt @{thm trans[OF comp_assoc[symmetric]]},
          rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
          rtac ctxt trans,
          rtac ctxt (#Map_comp (#axioms param)),
          rtac ctxt ext,
          rtac ctxt (#Map_cong (#axioms param)),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (maps (map #Sb_comp o axioms_of_bmv_monad) inners'),
            REPEAT_DETERM o assume_tac ctxt,
            rtac ctxt refl
          ]
        ],
        Vrs_bds = map (map (Option.map (K (fn ctxt => EVERY1 [
          REPEAT_DETERM o resolve_tac ctxt (
            maps (map_filter I) (#Vrs_bds axioms)
            @ maps (maps (maps (map_filter I) o #Vrs_bds) o axioms_of_bmv_monad) inners'
            @ #Supp_bd (#axioms param)
            @ map (fn thm =>
              thm OF [bd_infinite_regular_card_order_of_bmv_monad outer]
            ) @{thms infinite_regular_card_order_Un infinite_regular_card_order_UN}
          )
        ])))) Vrs,
        Vrs_Injs = map (map (Option.map (fn thm => fn ctxt =>
          print_tac ctxt "Vrs_Injs"
        ))) (#Vrs_Injs axioms),
        Vrs_Sbs = map (map (Option.map (K (fn ctxt => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt @{thms UN_Un}),
          REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
          REPEAT_DETERM o FIRST' [
            EVERY' [
              rtac ctxt @{thm trans[OF arg_cong[OF comp_apply]]},
              rtac ctxt trans,
              resolve_tac ctxt (maps (map_filter I) (#Map_Vrs param)),
              rtac ctxt trans,
              resolve_tac ctxt (maps (map_filter I) (#Vrs_Sbs axioms)),
              REPEAT_DETERM o assume_tac ctxt,
              rtac ctxt refl
            ],
            EVERY' [
              rtac ctxt trans,
              rtac ctxt @{thm arg_cong[of _ _ "\<lambda>x. \<Union>(_ ` x)"]},
              rtac ctxt trans,
              rtac ctxt @{thm trans[OF arg_cong[OF comp_apply]]},
              resolve_tac ctxt (#Supp_Map (#axioms param)),
              rtac ctxt @{thm arg_cong[of _ _ "\<lambda>x. _ ` x"]},
              resolve_tac ctxt (#Supp_Sb param),
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms UN_simps(10)}),
              rtac ctxt trans,
              rtac ctxt @{thm UN_cong},
              resolve_tac ctxt (maps (maps (maps (map_filter I) o #Vrs_Sbs) o axioms_of_bmv_monad) inners'),
              REPEAT_DETERM o assume_tac ctxt,
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms UN_extend_simps(9)}),
              rtac ctxt refl
            ]
          ]
        ])))) Vrs,
        Sb_cong = fn ctxt => EVERY1 [
          rtac ctxt @{thm comp_apply_eq},
          Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
            rtac ctxt @{thm trans[rotated]},
            rtac ctxt (
              let val n = length (lives_of_bmv_monad outer);
              in mk_arg_cong lthy (n + 1) (#Map param) OF (replicate n refl) end
            ),
            K (prefer_tac 2),
            rtac ctxt (#Map_cong (#axioms param)),
            K (Local_Defs.unfold0_tac ctxt (#Supp_Sb param)),
            EVERY' (map (fn Inr _ => rtac ctxt refl | Inl inner => EVERY' [
              resolve_tac ctxt (map #Sb_cong (axioms_of_bmv_monad inner)),
              REPEAT_DETERM o EVERY' [
                REPEAT_DETERM o resolve_tac ctxt prems,
                rotate_tac ~1,
                etac ctxt @{thm contrapos_pp},
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms bex_simps(8) Un_iff UN_iff de_Morgan_disj}),
                REPEAT_DETERM o etac ctxt conjE,
                dtac ctxt @{thm bspec[rotated]},
                assume_tac ctxt,
                assume_tac ctxt
              ]
            ]) inners),
            rtac ctxt (#Sb_cong axioms),
            REPEAT_DETERM o EVERY' [
              resolve_tac ctxt prems,
              TRY o EVERY' [
                etac ctxt @{thm contrapos_pp},
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
                REPEAT_DETERM o etac ctxt conjE,
                assume_tac ctxt
              ]
            ]
          ]) ctxt
        ]
      } : (Proof.context -> tactic) bmv_monad_axioms)
      (map (nth (axioms_of_bmv_monad outer)) idxs)
      (map (the o nth (params_of_bmv_monad outer)) idxs)
      Injs Vrs outer_Vrs
    } : (Proof.context -> tactic) bmv_monad_model;

    val (res, lthy) = bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Dont_Note) qualify model lthy
  in (res, lthy) end;

fun pbmv_monad_cmd ((((((b, ops), Sbs), Injs), Vrs), param_opt), bd) lthy =
  let
    val ops = map (Syntax.read_typ lthy) ops;
    val bd = Syntax.read_term lthy bd;
    val Sbs = map (Syntax.read_term lthy) Sbs;
    val frees = distinct (op=) (maps (
      map (fst o dest_funT) o fst o split_last o binder_types o fastype_of
    ) Sbs);
    val Injs = map (map (Syntax.read_term lthy)) Injs;
    val Vrs = map (map (map (fn "_" => NONE | t => SOME (Syntax.read_term lthy t)))) Vrs;

    val b = if Binding.is_empty b then fst (dest_Type (hd ops)) else Local_Theory.full_name lthy b

    val goals = mk_bmv_monad_axioms ops bd Sbs Injs Vrs [] lthy;

    fun after_qed thmss lthy =
      let
        val thms = map hd thmss;
        val model = {
          ops = ops,
          bd = bd,
          var_class = @{class var}, (* TODO: change *)
          leader = 0,
          frees = frees,
          lives = [],
          lives' = [],
          bmv_ops = [],
          params = replicate (length ops) NONE,
          Injs = Injs,
          Sbs = Sbs,
          Vrs = Vrs,
          bd_infinite_regular_card_order = hd thms,
          tacs = fst (fold_map (fn goal => fn thms =>
            let
              val chop_many = fold_map (fold_map (
                fn NONE => (fn thms => (NONE, thms))
                | SOME _ => fn thms => (SOME (hd thms), tl thms)
              ));
              val ((((((Sb_Inj, Sb_comp_Injs), Sb_comp), Vrs_bds), Vrs_Injs), Vrs_Sbs), thms) = thms
                |> apfst hd o chop 1
                ||>> chop (length (#Sb_comp_Injs goal))
                ||>> apfst hd o chop 1
                ||>> chop_many (#Vrs_bds goal)
                ||>> chop_many (#Vrs_Injs goal)
                ||>> chop_many (#Vrs_Sbs goal);
            in ({
              Sb_Inj = Sb_Inj,
              Sb_comp_Injs = Sb_comp_Injs,
              Sb_comp = Sb_comp,
              Vrs_bds = Vrs_bds,
              Vrs_Injs = Vrs_Injs,
              Vrs_Sbs = Vrs_Sbs,
              Sb_cong = hd thms
            }: thm bmv_monad_axioms, thms) end
          ) goals (tl thms))
        } : thm bmv_monad_model;

        val (bmv, lthy) = mk_bmv_monad BNF_Def.Smart_Inline (K BNF_Def.Note_Some) model lthy;

        val lthy = register_pbmv_monad b bmv lthy;
      in lthy end;
  in Proof.theorem NONE after_qed (map (single o rpair []) (
    [HOLogic.mk_Trueprop (mk_infinite_regular_card_order bd)]
    @ maps (fn goal => #Sb_Inj goal :: #Sb_comp_Injs goal @ [#Sb_comp goal]
      @ maps (map_filter I) (#Vrs_bds goal @ #Vrs_Injs goal @ #Vrs_Sbs goal)
      @ [#Sb_cong goal]
    ) goals
  )) lthy
    |> Proof.refine_singleton (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (TRYALL (rtac ctxt refl))))
  end;

fun print_pbmv_monads ctxt =
  let
    fun pretty_mrbnf (key, BMV {ops, frees, lives, bd, Sbs, ...}) =
      Pretty.big_list
        (Pretty.string_of (Pretty.block ([Pretty.str key, Pretty.str ":", Pretty.brk 1] @
          map (Pretty.quote o Syntax.pretty_typ ctxt) ops)))
        ([Pretty.block [Pretty.str "frees:", Pretty.brk 1, Pretty.str (string_of_int (length frees)),
            Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) frees)]] @
          (if length lives > 0 then
            [Pretty.block [Pretty.str "live:", Pretty.brk 1, Pretty.str (string_of_int (length lives)),
              Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) lives)]]
          else []) @
          [ Pretty.block ([Pretty.str "Sb:", Pretty.brk 1] @ map (Pretty.quote o Syntax.pretty_term ctxt) Sbs),
            Pretty.block [Pretty.str ("bd:"), Pretty.brk 1,
            Pretty.quote (Syntax.pretty_term ctxt bd)]]);
  in
    Pretty.big_list "Registered parametrized bounded multi-variate monads:"
      (map pretty_mrbnf (sort_by fst (Symtab.dest (Data.get (Context.Proof ctxt)))))
    |> Pretty.writeln
  end;

val _ =
  Outer_Syntax.command @{command_keyword print_pbmv_monads}
    "print all parametrized bounded multi-variate monads"
    (Scan.succeed (Toplevel.keep (print_pbmv_monads o Toplevel.context_of)));

val _ = Outer_Syntax.local_theory_to_proof @{command_keyword pbmv_monad}
  "register a parametrized bounded multi-variate monad"
  (parse_opt_binding_colon -- Scan.repeat1 (Scan.unless (Parse.reserved "Sbs") Parse.typ) --|
    (Parse.reserved "Sbs" -- @{keyword ":"}) -- Scan.repeat1 (Scan.unless (Parse.reserved "Injs") Parse.term) --|
    (Parse.reserved "Injs" -- @{keyword ":"}) -- Parse.list (Scan.repeat1 (Scan.unless (Parse.reserved "Vrs") Parse.term)) --|
    (Parse.reserved "Vrs" -- @{keyword ":"}) -- Parse.and_list (Parse.list (
      Scan.repeat1 (Scan.unless (Parse.reserved "Map" || Parse.reserved "bd") (Parse.term || Parse.reserved "_"))
    )) --
    Scan.optional (
      (Parse.reserved "Map" -- @{keyword ":"}) |-- Scan.repeat1 (Scan.unless (Parse.reserved "Supps") Parse.term) --|
      (Parse.reserved "Supps" -- @{keyword ":"}) -- Parse.list (Scan.repeat1 (Scan.unless (Parse.reserved "bd") Parse.term))
      >> SOME
    ) NONE --|
    (Parse.reserved "bd" -- @{keyword ":"}) -- Parse.term
  >> pbmv_monad_cmd)

end