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

  type 'a bmv_monad_consts = {
    bd: term,
    params: { Map: term, Supps: term list} option list,
    Injs: term list list,
    SSupps: 'a list list,
    Sbs: term list,
    Vrs: term option list list list
  };

  type 'a bmv_monad_param = {
    axioms: 'a supported_functor_axioms,
    Map_Sb: 'a,
    Supp_Sb: 'a list,
    Map_Vrs: 'a option list list
  };

  type 'a bmv_monad_model = {
    ops: typ list,
    var_class: class,
    bmv_ops: bmv_monad list,
    frees: typ list,
    deads: typ list,
    leader: int,
    lives: typ list,
    lives': typ list,
    consts: (term option) bmv_monad_consts,
    params: 'a bmv_monad_param option list,
    bd_infinite_regular_card_order: 'a,
    SSupp_eq: 'a option list list,
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
  val deads_of_bmv_monad: bmv_monad -> typ list;
  val Injs_of_bmv_monad: bmv_monad -> term list list;
  val SSupps_of_bmv_monad: bmv_monad -> (term * thm) list list;
  val Sbs_of_bmv_monad: bmv_monad -> term list;
  val Maps_of_bmv_monad: bmv_monad -> term option list;
  val Supps_of_bmv_monad: bmv_monad -> term list option list;
  val Vrs_of_bmv_monad: bmv_monad -> term option list list list;
  val axioms_of_bmv_monad: bmv_monad -> thm bmv_monad_axioms list;
  val params_of_bmv_monad: bmv_monad -> {
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

  val compose_bmv_monad: (binding -> binding) -> bmv_monad -> (bmv_monad, typ) MRBNF_Util.either list
    -> local_theory -> (bmv_monad * thm list) * local_theory
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
  axioms: 'a supported_functor_axioms,
  Map_Sb: 'a,
  Supp_Sb: 'a list,
  Map_Vrs: 'a option list list
};

fun map_bmv_monad_param f ({ axioms, Map_Sb, Supp_Sb, Map_Vrs }: 'a bmv_monad_param) = {
  axioms = map_supported_functor_axioms f axioms,
  Map_Sb = f Map_Sb,
  Supp_Sb = map f Supp_Sb,
  Map_Vrs = map (map (Option.map f)) Map_Vrs
}: 'b bmv_monad_param;


type 'a bmv_monad_consts = {
  bd: term,
  params: { Map: term, Supps: term list} option list,
  Injs: term list list,
  SSupps: 'a list list,
  Sbs: term list,
  Vrs: term option list list list
};

fun morph_bmv_monad_consts phi f { bd, params, Injs, SSupps, Sbs, Vrs } = {
  bd = Morphism.term phi bd,
  params = map (Option.map (fn { Map, Supps } => {
    Map = Morphism.term phi Map,
    Supps = map (Morphism.term phi) Supps
  })) params,
  Injs = map (map (Morphism.term phi)) Injs,
  SSupps = map (map f) SSupps,
  Sbs = map (Morphism.term phi) Sbs,
  Vrs = map (map (map (Option.map (Morphism.term phi)))) Vrs
}: 'a bmv_monad_consts;

datatype bmv_monad = BMV of {
  ops: typ list,
  var_class: class,
  leader: int,
  frees: typ list,
  lives: typ list,
  lives': typ list,
  deads: typ list,
  consts: (term * thm) bmv_monad_consts,
  params: thm bmv_monad_param option list,
  bd_infinite_regular_card_order: thm,
  axioms: thm bmv_monad_axioms list
}

fun morph_bmv_monad phi (BMV {
  ops, var_class, leader, frees, lives, lives', deads, consts, params, axioms, bd_infinite_regular_card_order
}) = BMV {
  ops = map (Morphism.typ phi) ops,
  leader = leader,
  var_class = var_class,
  frees = map (Morphism.typ phi) frees,
  lives = map (Morphism.typ phi) lives,
  lives' = map (Morphism.typ phi) lives',
  deads = map (Morphism.typ phi) deads,
  consts = morph_bmv_monad_consts phi (map_prod (Morphism.term phi) (Morphism.thm phi)) consts,
  params = map (Option.map (map_bmv_monad_param (Morphism.thm phi))) params,
  axioms = map (morph_bmv_monad_axioms phi) axioms,
  bd_infinite_regular_card_order = Morphism.thm phi bd_infinite_regular_card_order
}

fun Rep_bmv (BMV x) = x

val ops_of_bmv_monad = #ops o Rep_bmv
val bd_of_bmv_monad = #bd o #consts o Rep_bmv
val var_class_of_bmv_monad = #var_class o Rep_bmv;
val leader_of_bmv_monad = #leader o Rep_bmv
val frees_of_bmv_monad = #frees o Rep_bmv
val lives_of_bmv_monad = #lives o Rep_bmv
val lives'_of_bmv_monad = #lives' o Rep_bmv
val deads_of_bmv_monad = #deads o Rep_bmv
val Injs_of_bmv_monad = #Injs o #consts o Rep_bmv
val SSupps_of_bmv_monad = #SSupps o #consts o Rep_bmv
val Sbs_of_bmv_monad = #Sbs o #consts o Rep_bmv
val Maps_of_bmv_monad = map (Option.map #Map) o #params o #consts o Rep_bmv
val Supps_of_bmv_monad = map (Option.map #Supps) o #params o #consts o Rep_bmv
val Vrs_of_bmv_monad = #Vrs o #consts o Rep_bmv
val axioms_of_bmv_monad = #axioms o Rep_bmv
val params_of_bmv_monad = #params o Rep_bmv
val bd_infinite_regular_card_order_of_bmv_monad = #bd_infinite_regular_card_order o Rep_bmv

type 'a bmv_monad_model = {
  ops: typ list,
  var_class: class,
  frees: typ list,
  lives: typ list,
  lives': typ list,
  deads: typ list,
  consts: (term option) bmv_monad_consts,
  params: 'a bmv_monad_param option list,
  bmv_ops: bmv_monad list,
  leader: int,
  bd_infinite_regular_card_order: 'a,
  SSupp_eq: 'a option list list,
  tacs: 'a bmv_monad_axioms list
}

fun morph_bmv_monad_model phi f ({ ops, var_class, frees, lives, lives', consts, bmv_ops, leader,
  params, tacs, bd_infinite_regular_card_order, deads, SSupp_eq }
) = {
  ops = map (Morphism.typ phi) ops,
  var_class = var_class,
  frees = map (Morphism.typ phi) frees,
  lives = map (Morphism.typ phi) lives,
  lives' = map (Morphism.typ phi) lives',
  deads = map (Morphism.typ phi) deads,
  consts = morph_bmv_monad_consts phi (Option.map (Morphism.term phi)) consts,
  params = params,
  bmv_ops = map (morph_bmv_monad phi) bmv_ops,
  leader = leader,
  tacs = map (map_bmv_monad_axioms f) tacs,
  SSupp_eq = map (map (Option.map f)) SSupp_eq,
  bd_infinite_regular_card_order = bd_infinite_regular_card_order
} : 'b bmv_monad_model;

fun update_consts consts (model: 'a bmv_monad_model) = {
  ops = #ops model,
  var_class = #var_class model,
  frees = #frees model,
  lives = #lives model,
  lives' = #lives' model,
  deads = #deads model,
  consts = consts,
  params = #params model,
  bmv_ops = #bmv_ops model,
  leader = #leader model,
  tacs = #tacs model,
  SSupp_eq = #SSupp_eq model,
  bd_infinite_regular_card_order = #bd_infinite_regular_card_order model
}: 'a bmv_monad_model;

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

val mk_small_prems = map2 (fn rho => fn SSupp => HOLogic.mk_Trueprop (mk_ordLess
  (mk_card_of (the SSupp $ rho))
  (mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of rho))))
));

fun mk_bmv_monad_axioms ops consts SSupp_defs bmv_ops lthy =
  let
    val Ts = ops @ maps ops_of_bmv_monad bmv_ops;
    val Sbs = #Sbs consts @ maps Sbs_of_bmv_monad bmv_ops;
    val Injss = #Injs consts @ maps Injs_of_bmv_monad bmv_ops;
    val Vrss = #Vrs consts @ maps Vrs_of_bmv_monad bmv_ops;

    val (axioms, SSupp_eq) = split_list (@{map 6} (fn T => fn Injs => fn SSupps => fn SSupp_defs => fn Sb => fn Vrs =>
      let
        val (own_Injs, other_Injs) = partition (fn Inj => body_type (fastype_of Inj) = T) Injs;
        val is_own_Inj = map (curry (op=) T o body_type o fastype_of) Injs;
        val other_idxs = map (fn Inj => find_index (fn T => body_type (fastype_of Inj) = T) Ts) other_Injs;
        val ((((rhos, rhos'), aa), x), _) = lthy
          |> mk_Frees "\<rho>" (map fastype_of Injs)
          ||>> mk_Frees "\<rho>'" (map fastype_of Injs)
          ||>> mk_Frees "a" (map (fst o dest_funT o fastype_of) Injs)
          ||>> apfst hd o mk_Frees "x" [T];
        val nown = length own_Injs;
        val (own_rhos, other_rhos) = chop nown rhos;

        val Sb_Inj = mk_Trueprop_eq (Term.list_comb (Sb, Injs), HOLogic.id_const T);

        val small_prems = mk_small_prems rhos SSupps;
        val small_prems' = mk_small_prems rhos' SSupps;

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
          HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (Vrs $ x)) (#bd consts))
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

        val SSupp_eq = @{map 4} (fn Inj => fn rho => fn SSupp => (fn NONE =>
          SOME (Logic.all rho (mk_Trueprop_eq (
            the SSupp $ rho, HOLogic.mk_Collect ("a", domain_type (fastype_of rho), HOLogic.mk_not (HOLogic.mk_eq (
              rho $ Bound 0, Inj $ Bound 0
            )))
          )))
          | SOME _ => NONE
        )) Injs rhos SSupps SSupp_defs;
      in ({
        Sb_Inj = Sb_Inj,
        Sb_comp_Injs = Sb_comp_Injs,
        Sb_comp = Sb_comp,
        Vrs_Injs = Vrs_Injs,
        Vrs_bds = Vrs_bds,
        Vrs_Sbs = Vrs_Sbs,
        Sb_cong = Sb_cong
      } : term bmv_monad_axioms, SSupp_eq) end
    ) ops (#Injs consts) (#SSupps consts) SSupp_defs (#Sbs consts) (#Vrs consts));
  in (axioms, SSupp_eq) end;

fun mk_param_axiom Map Supps SSupps Sb Injs Vrs bd lthy =
  let
    val (f_Ts, T) = split_last (binder_types (fastype_of Map));
    val (lives, lives') = split_list (map dest_funT f_Ts);

    val (Cs, _) = lthy
      |> mk_TFrees (length lives);
    val ((((fs, gs), rhos), x), _) = lthy
      |> mk_Frees "f" (map2 (curry (op-->)) lives lives')
      ||>> mk_Frees "g" (map2 (curry (op-->)) lives' Cs)
      ||>> mk_Frees "\<rho>" (map fastype_of Injs)
      ||>> apfst hd o mk_Frees "x" [T];;

    val Map_id = Term.subst_atomic_types (lives' ~~ lives) (
      mk_Trueprop_eq (
        Term.list_comb (Map, map HOLogic.id_const lives), HOLogic.id_const T
      )
    );

    val Map_comp = fold_rev Logic.all (fs @ gs) (mk_Trueprop_eq (
      HOLogic.mk_comp (Term.list_comb (
        Term.subst_atomic_types ((lives @ lives') ~~ (lives' @ Cs)) Map, gs
      ), Term.list_comb (Map, fs)),
      Term.list_comb (Term.subst_atomic_types (lives' ~~ Cs) Map, map2 (curry HOLogic.mk_comp) gs fs)
    ));

    val Supp_Maps = map2 (fn Supp => fn f =>
      fold_rev Logic.all (fs @ [x]) (mk_Trueprop_eq (
        Term.subst_atomic_types (lives ~~ lives') Supp $ (Term.list_comb (Map, fs) $ x),
        mk_image f $ (Supp $ x)
      ))
    ) Supps fs;

    val Supp_bds = map (fn Supp => Logic.all x (HOLogic.mk_Trueprop (
      mk_ordLess (mk_card_of (Supp $ x)) bd
    ))) Supps;

    val (gs', _) = lthy
      |> mk_Frees "g" (map fastype_of fs);
    val Map_cong = fold_rev Logic.all (fs @ gs' @ [x]) (
      fold_rev (curry Logic.mk_implies) (@{map 3} (fn Supp => fn f => fn g =>
        let val a = Free ("a", hd (binder_types (fastype_of f)));
        in Logic.all a (Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Supp $ x)),
          mk_Trueprop_eq (f $ a, g $ a)
        )) end
      ) Supps fs gs') (mk_Trueprop_eq (
        Term.list_comb (Map, fs) $ x,
        Term.list_comb (Map, gs') $ x
      )));

    val Map_Sb = fold_rev Logic.all (fs @ rhos) (
      fold_rev (curry Logic.mk_implies) (mk_small_prems rhos SSupps) (mk_Trueprop_eq (
        HOLogic.mk_comp (Term.list_comb (Map, fs), Term.list_comb (Sb, rhos)),
        HOLogic.mk_comp (Term.list_comb (
          Term.subst_atomic_types (lives ~~ lives') Sb, rhos
        ), Term.list_comb (Map, fs))
      ))
    );

    val Map_Vrs = map (map (Option.map (fn Vrs =>
      fold_rev Logic.all (fs @ [x]) (mk_Trueprop_eq (
        Term.subst_atomic_types (lives ~~ lives') Vrs $ (Term.list_comb (Map, fs) $ x),
        Vrs $ x
      ))
    ))) Vrs;

    val Supp_Sb = map (fn Supp =>
      fold_rev Logic.all (rhos @ [x]) (mk_Trueprop_eq (
        Supp $ (Term.list_comb (Sb, rhos) $ x), Supp $ x
      ))
    ) Supps;
  in {
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
  }: term bmv_monad_param end;

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

fun define_bmv_monad_consts const_policy fact_policy qualify leader ops lives' (consts: (term option) bmv_monad_consts) lthy =
  let
    val maybe_define' = maybe_define const_policy fact_policy o qualify;

    val suffixes = map_index (fn (i, T) => Binding.suffix_name ("_" ^ (case T of
      Type (n, Ts) => if forall Term.is_TFree Ts then short_type_name n else string_of_int i
      | _ => string_of_int i
    ))) ops;
    val suffixess = map2 (fn suffix => fn Injs => case Injs of
      [_] => [suffix]
      | _ => map_index (fn (i, _) => Binding.suffix_name ("_" ^ string_of_int i) o suffix) Injs
    ) suffixes (#Injs consts);

    val (_, lthy) = Local_Theory.begin_nested lthy;
    val ((Sbs, Sb_defs), lthy) = apfst split_list (@{fold_map 2} (fn Sb => fn suffix =>
      maybe_define' (suffix (Binding.name "Sb")) Sb
    ) (#Sbs consts) suffixes lthy);

    val ((Injs, Inj_defs), lthy) = apfst (split_list o map split_list) (@{fold_map 2} (
      @{fold_map 2} (fn Inj => fn suffix => maybe_define' (suffix (Binding.name "Inj")) Inj)
    ) (#Injs consts) suffixess lthy);

    val ((SSupps, SSupp_defs), lthy) = apfst (split_list o map split_list) (@{fold_map 3} (@{fold_map 3} (
      fn Inj => fn suffix => fn SSupp_opt => fn lthy => case SSupp_opt of
        SOME t => ((t, NONE), lthy)
        | NONE => apfst (apsnd SOME) (MRBNF_Util.mk_def_t true Binding.empty I (Binding.name_of (suffix (Binding.name "SSupp"))) 1 (
          Term.absfree ("\<rho>", fastype_of Inj) (HOLogic.mk_Collect ("a", domain_type (fastype_of Inj),
            HOLogic.mk_not (HOLogic.mk_eq (Free ("\<rho>", fastype_of Inj) $ Bound 0, Inj $ Bound 0))
          ))
        ) lthy)
      )
    ) (#Injs consts) suffixess (#SSupps consts) lthy);

    val (Vrs', lthy) =
      (@{fold_map 2} (@{fold_map 2} (fn suffix => fn Vrs => @{fold_map 2} (fn i => fold_map_option (fn Vrs =>
        maybe_define' (Binding.suffix_name ("_" ^ string_of_int i) (suffix (Binding.name "Vrs"))) Vrs
      )) (0 upto length Vrs - 1) Vrs)) suffixess (#Vrs consts) lthy);

    val Vrs = map (map (map (Option.map fst))) Vrs';
    val Vrs_defs = maps (maps (map (Option.mapPartial snd))) Vrs';

    val (params', lthy) = @{fold_map 2} (fn suffix => fold_map_option (fn param => fn lthy =>
      let
        val ((Map, Map_def), lthy) = maybe_define' (suffix (Binding.name "Map")) (#Map param) lthy;
        val ((Supps, Supp_defs), lthy) = apfst split_list (@{fold_map 2} (fn i =>
          maybe_define' (Binding.suffix_name ("_" ^ string_of_int i) (suffix (Binding.name "Supp")))
        ) (0 upto length (#Supps param) - 1) (#Supps param) lthy);
        val param = {
          Map = Map,
          Supps = Supps
        };
      in ((param, Map_def :: Supp_defs), lthy) end
    )) suffixes (#params consts) lthy;
    val params = map (Option.map fst) params';
    val param_defs = map_filter (Option.map snd) params';

    val ((bd, bd_def), lthy) = maybe_define' (Binding.name "bd") (#bd consts) lthy;

    val consts' = {
      bd = bd,
      params = params,
      Injs = Injs,
      SSupps = map (map SOME) SSupps,
      Sbs = Sbs,
      Vrs = Vrs
    } : (term option) bmv_monad_consts;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val vars = map TFree (rev (Term.add_tfreesT (nth ops leader) [])) @ lives';
    val subst = (map (Morphism.typ phi) vars ~~ vars);

    val phi' = Morphism.term_morphism "bmv_monad_export" (Term.subst_atomic_types subst o Morphism.term phi)
    val consts' = morph_bmv_monad_consts phi' (Option.map (Morphism.term phi')) consts';

    val defs = map_filter I (Sb_defs @ flat Inj_defs @ Vrs_defs @ [bd_def] @ flat param_defs);
  in (consts', map (Morphism.thm phi) defs, map (map (Option.map (Morphism.thm phi))) SSupp_defs, lthy) end;

fun mk_bmv_monad const_policy fact_policy SSupp_defs (model: thm bmv_monad_model) lthy =
  let
    (* TODO: Derived theorems *)

    val SSupp_defs = map2 (map2 (fn SOME def => K def
      | NONE => fn thm => @{thm eq_reflection} OF [the thm]
    )) SSupp_defs (#SSupp_eq model);
    val consts = {
      bd = #bd (#consts model),
      params = #params (#consts model) @ maps (#params o #consts o Rep_bmv) (#bmv_ops model),
      Injs = #Injs (#consts model) @ maps (#Injs o #consts o Rep_bmv) (#bmv_ops model),
      SSupps = map2 (map2 (pair o the)) (#SSupps (#consts model)) SSupp_defs @ maps (#SSupps o #consts o Rep_bmv) (#bmv_ops model),
      Sbs = #Sbs (#consts model) @ maps (#Sbs o #consts o Rep_bmv) (#bmv_ops model),
      Vrs = #Vrs (#consts model) @ maps (#Vrs o #consts o Rep_bmv) (#bmv_ops model)
    };
    val bmv = BMV {
      ops = #ops model @ maps (#ops o Rep_bmv) (#bmv_ops model),
      var_class = #var_class model,
      leader = #leader model,
      frees = #frees model,
      lives = #lives model,
      lives' = #lives' model,
      deads = #deads model,
      consts = consts,
      params = #params model @ maps (#params o Rep_bmv) (#bmv_ops model),
      axioms = #tacs model @ maps (#axioms o Rep_bmv) (#bmv_ops model),
      bd_infinite_regular_card_order = #bd_infinite_regular_card_order model
    } : bmv_monad;
  in (bmv, lthy) end

fun prove_axioms (model: (Proof.context -> tactic) bmv_monad_model) defs SSupp_defs lthy =
  let
    val (goals, SSupp_eq) = mk_bmv_monad_axioms (#ops model) (#consts model) SSupp_defs (#bmv_ops model) lthy;
    val tacs' = map (map_bmv_monad_axioms (fn tac => fn ctxt => Local_Defs.unfold0_tac ctxt defs THEN tac ctxt)) (#tacs model);
  in (map2 apply_bmv_monad_axioms
    (map (map_bmv_monad_axioms (fn goal => fn tac => Goal.prove_sorry lthy [] [] goal (tac o #context))) goals)
    tacs',
    map2 (map2 (fn tac => Option.map (fn SSupp_eq => Goal.prove_sorry lthy [] [] SSupp_eq (fn {context=ctxt, ...} =>
      Local_Defs.unfold0_tac ctxt defs THEN the tac ctxt
    )))) (#SSupp_eq model) SSupp_eq
  )
  end;

fun prove_params (model: (Proof.context -> tactic) bmv_monad_model) defs lthy =
  let
    val goals = @{map 5} (fn Sb => fn Vrs => fn Injs => fn SSupps => Option.map (fn param =>
      mk_param_axiom (#Map param) (#Supps param) SSupps Sb Injs Vrs (#bd (#consts model)) lthy
    )) (#Sbs (#consts model)) (#Vrs (#consts model)) (#Injs (#consts model)) (#SSupps (#consts model)) (#params (#consts model))
    val tacs' = map (Option.map (map_bmv_monad_param (fn tac => fn goal =>
      Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, ...} =>
       Local_Defs.unfold0_tac ctxt defs THEN tac ctxt
     )
    ))) (#params model);
  in map2 (@{map_option 2} (
    fn { axioms=tacs, Map_Sb=f1, Supp_Sb=f2s, Map_Vrs=f3s, ...} =>
    fn { axioms, Map_Sb, Supp_Sb, Map_Vrs } => {
      Map_Sb = f1 Map_Sb, Supp_Sb = map2 (curry (op|>)) Supp_Sb f2s,
      Map_Vrs = map2 (map2 (@{map_option 2} (curry (op|>)))) Map_Vrs f3s, axioms = {
        Map_id = #Map_id tacs (#Map_id axioms),
        Map_comp = #Map_comp tacs (#Map_comp axioms),
        Supp_Map = map2 (curry (op|>)) (#Supp_Map axioms) (#Supp_Map tacs),
        Supp_bd = map2 (curry (op|>)) (#Supp_bd axioms) (#Supp_bd tacs),
        Map_cong = #Map_cong tacs (#Map_cong axioms)
      }
  } : thm bmv_monad_param)) tacs' goals end;

fun mk_thm_model (model: 'a bmv_monad_model) params axioms SSupp_eq bd_irco = {
  ops = #ops model,
  var_class = #var_class model,
  leader = #leader model,
  frees = #frees model,
  lives = #lives model,
  lives' = #lives' model,
  deads = #deads model,
  bmv_ops = #bmv_ops model,
  consts = #consts model,
  params = params,
  bd_infinite_regular_card_order = bd_irco,
  SSupp_eq = SSupp_eq,
  tacs = axioms
} : thm bmv_monad_model;

fun bmv_monad_def const_policy fact_policy qualify (model: (Proof.context -> tactic) bmv_monad_model) lthy =
  let
    val frees = map (fn T => TFree (apsnd (
      Sign.minimize_sort (Proof_Context.theory_of lthy) o cons (#var_class model)
    ) (dest_TFree T))) (#frees model);
    val model = morph_bmv_monad_model (MRBNF_Util.subst_typ_morphism (#frees model ~~ frees)) I model;

    val (consts, unfold_set, SSupp_defs, lthy) = define_bmv_monad_consts const_policy (fact_policy lthy) qualify
      (#leader model) (#ops model) (#lives' model) (#consts model) lthy;
    val model = update_consts consts model;

    val (axioms, SSupp_eq) = prove_axioms model unfold_set SSupp_defs lthy;
    val params = prove_params model unfold_set lthy;

    val bd_irco = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (
      mk_infinite_regular_card_order (#bd (#consts model))
    )) (fn {context=ctxt, ...} => Local_Defs.unfold0_tac ctxt unfold_set THEN #bd_infinite_regular_card_order model ctxt);

    val model = mk_thm_model model params axioms SSupp_eq bd_irco;
  in apfst (rpair unfold_set) (mk_bmv_monad const_policy fact_policy SSupp_defs model lthy) end

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
     var_class = var_class,
     leader = 0,
     frees = [],
     lives = lives,
     lives' = lives',
     deads = deads,
     bmv_ops = [],
     consts = {
       bd = BNF_Def.bd_of_bnf bnf,
       Injs = [[]],
       SSupps = [[]],
       Sbs = [HOLogic.id_const T],
       Vrs = [[]],
       params = [SOME {
         Map = BNF_Def.mk_map_of_bnf deads lives lives' bnf,
         Supps = BNF_Def.mk_sets_of_bnf (replicate n deads) (replicate n lives) bnf
       }]
     },
     params = [SOME {
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
     bd_infinite_regular_card_order = fn ctxt => EVERY1 [
       rtac ctxt @{thm infinite_regular_card_order.intro},
       rtac ctxt (BNF_Def.bd_card_order_of_bnf bnf),
       rtac ctxt (BNF_Def.bd_cinfinite_of_bnf bnf),
       rtac ctxt (BNF_Def.bd_regularCard_of_bnf bnf)
     ],
     SSupp_eq = [[]],
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

fun slice_bmv_monad n bmv =
  let
    fun f xs = nth xs n;
    val Sb = f (Sbs_of_bmv_monad bmv);
    val vars = map TFree (Term.add_tfrees Sb []);
  in BMV {
    ops = [f (ops_of_bmv_monad bmv)],
    var_class = var_class_of_bmv_monad bmv,
    leader = 0,
    frees = filter (member (op=) vars) (frees_of_bmv_monad bmv),
    lives = lives_of_bmv_monad bmv,
    lives' = lives'_of_bmv_monad bmv,
    deads = deads_of_bmv_monad bmv,
    consts = {
      bd = bd_of_bmv_monad bmv,
      params = [@{map_option 2} (fn Map => fn Supps => {
        Map = Map, Supps = Supps
      }) (f (Maps_of_bmv_monad bmv)) (f (Supps_of_bmv_monad bmv))],
      Injs = [f (Injs_of_bmv_monad bmv)],
      SSupps = [f (SSupps_of_bmv_monad bmv)],
      Sbs = [Sb],
      Vrs = [f (Vrs_of_bmv_monad bmv)]
    },
    params = [f (params_of_bmv_monad bmv)],
    bd_infinite_regular_card_order = bd_infinite_regular_card_order_of_bmv_monad bmv,
    axioms = [f (axioms_of_bmv_monad bmv)]
  } end;

fun compose_bmv_monad qualify (outer : bmv_monad) (inners : (bmv_monad, typ) either list) lthy =
  let
    val _ = if length (lives_of_bmv_monad outer) <> length inners then
      error "Outer needs exactly as many lives as there are inners" else ()

    val filter_bmvs = map_filter (fn Inl x => SOME x | _ => NONE);

    fun vars_of_bmv_monad bmv = @{fold 2} (fn T => fn Map => case Map of
      SOME t => Term.add_tfrees t
      | NONE => Term.add_tfreesT T
    ) (ops_of_bmv_monad bmv) (Maps_of_bmv_monad bmv) [];

    fun sum_collapse (Inl x) = x
      | sum_collapse (Inr x) = x

    val vars = fold (fn (n, s) =>
      Symtab.map_default (n, s) (curry (Sign.inter_sort (Proof_Context.theory_of lthy)) s)
    ) (vars_of_bmv_monad outer @ maps (
      sum_collapse o map_sum vars_of_bmv_monad (fn T => Term.add_tfreesT T [])
    ) inners) Symtab.empty;

    fun mk_sign_morph bmv =
      morph_bmv_monad (MRBNF_Util.subst_typ_morphism (map (fn (n, s) =>
        (TFree (n, s), TFree (n, the (Symtab.lookup vars n)))
      ) (vars_of_bmv_monad bmv))) bmv;
    fun mk_T_morph T =
      Term.typ_subst_atomic (map (fn x =>
        (TFree x, the_default (TFree x) (Option.map (TFree o pair (fst x)) (Symtab.lookup vars (fst x))))
      ) (Term.add_tfreesT T [])) T
    val outer = mk_sign_morph outer;
    val inners = map (map_sum mk_sign_morph mk_T_morph) inners;
    val inners' = filter_bmvs inners;

    val inner_leaders' = map (map_sum (fn bmv => slice_bmv_monad (leader_of_bmv_monad bmv) bmv) I) inners;
    val inner_leaders = map_filter (fn Inr _ => NONE | Inl bmv => SOME bmv) inner_leaders';

    val subst =
      let val Ts = map (sum_collapse o map_sum (hd o ops_of_bmv_monad) I) inner_leaders'
      in (lives_of_bmv_monad outer ~~ Ts) @ (lives'_of_bmv_monad outer ~~ Ts) end;
    val new_leader = Term.typ_subst_atomic subst (nth (ops_of_bmv_monad outer) (leader_of_bmv_monad outer));

    val new_Injs = distinct (op=) (
      map (Term.subst_atomic_types subst) (nth (Injs_of_bmv_monad outer) (leader_of_bmv_monad outer))
      @ maps (hd o Injs_of_bmv_monad) inner_leaders
    );
    val outer' = morph_bmv_monad (MRBNF_Util.subst_typ_morphism subst) outer;
    val minions = fold_rev (fn bmv => fold_rev (fn i => fn xs =>
      let val T = nth (ops_of_bmv_monad bmv) i;
      in if member (fn (a, b) => a = fst b) xs T
      then xs else (T, slice_bmv_monad i bmv) :: xs end
    ) (0 upto length (ops_of_bmv_monad bmv) - 1)) (outer' :: inners') [];
    val minions = map_filter (AList.lookup (op=) minions o body_type o fastype_of) new_Injs;

    val (lSSupps, SSuppss) = split_list (map (fn bmv => apfst hd (apply2 (map snd) (
      partition (fn (i, _) => i = leader_of_bmv_monad bmv)
        ((0 upto length (ops_of_bmv_monad bmv) - 1) ~~ SSupps_of_bmv_monad bmv)
    ))) (outer' :: inners'));
    val SSupps = flat (flat SSuppss) @ flat lSSupps;
    val new_SSupps = map (fn t =>
      the (List.find (fn (SSupp, _) => domain_type (fastype_of SSupp) = fastype_of t) SSupps)
    ) new_Injs;

    val ((fs, x), _) = lthy
      |> mk_Frees "f" (map fastype_of new_Injs)
      ||>> apfst hd o mk_Frees "x" [new_leader];

    fun leader f bmv = nth (f bmv) (leader_of_bmv_monad bmv);
    fun mk_Sb (Inl bmv) =
      let val Sb = leader Sbs_of_bmv_monad bmv;
      in Term.list_comb (Sb,
        map (fn T => the (List.find (curry (op=) T o fastype_of) fs)) (fst (split_last (binder_types (fastype_of Sb))))
      ) end
      | mk_Sb (Inr T) = HOLogic.id_const T;
    val new_Sb = fold_rev Term.absfree (map dest_Free fs) (HOLogic.mk_comp (
      Term.list_comb (the (leader Maps_of_bmv_monad outer'), map mk_Sb inners),
      mk_Sb (Inl outer')
    ));

    val frees = map TFree (rev (fold Term.add_tfrees new_Injs []));
    val new_Vrs = map (fn Inj =>
      let
        fun get_sets bmv =
          let val idx = find_index (curry ((op=) o apply2 fastype_of) Inj) (leader Injs_of_bmv_monad bmv);
          in if idx < 0 then [] else map_filter I (nth (leader Vrs_of_bmv_monad bmv) idx) end;

        val sets = flat (map (fn t => t $ x) (get_sets outer')
          :: @{map_filter 2} (fn Inr _ => K NONE | Inl bmv => fn Supp =>
            let val sets = get_sets bmv;
            in if null sets then NONE else SOME (map (mk_UNION (Supp $ x)) sets) end
          ) inners (the (leader Supps_of_bmv_monad outer'))
        );
      in map (fn var =>
        let
          val sets' = filter (curry (op=) var o HOLogic.dest_setT o fastype_of) sets;
        in if null sets' then NONE else SOME (Term.absfree (dest_Free x) (foldl1 mk_Un sets')) end
      ) frees end
    ) new_Injs;

    val ops = new_leader :: map (hd o ops_of_bmv_monad) minions;

    val vars = distinct (op=) (map TFree (fold Term.add_tfreesT ops []));
    val lives = distinct (op=) (maps lives_of_bmv_monad inners');

    val consts = {
      bd = bd_of_bmv_monad outer, (* TODO: compose bounds *)
      Injs = [new_Injs],
      Sbs = [new_Sb],
      Vrs = [new_Vrs],
      SSupps = [map (SOME o fst) new_SSupps],
      params = [NONE]
    }: (term option) bmv_monad_consts;

    val SSupp_defs = map snd (flat (maps SSupps_of_bmv_monad (outer' :: inners')));

    val model = {
      ops = [new_leader],
      bmv_ops = minions,
      bd_infinite_regular_card_order = fn ctxt => rtac ctxt (bd_infinite_regular_card_order_of_bmv_monad outer) 1,
      var_class = var_class_of_bmv_monad outer,
      frees = frees,
      lives = lives,
      lives' = distinct (op=) (maps lives'_of_bmv_monad inners'),
      deads = subtract (op=) (lives @ frees) vars,
      consts = consts,
      params = [NONE],
      leader = 0,
      SSupp_eq = [map (fn (_, thm) => SOME (fn ctxt =>
        Local_Defs.unfold0_tac ctxt [thm] THEN rtac ctxt refl 1
      )) new_SSupps],
      tacs = @{map 5} (fn axioms => fn param => fn Map => fn Injs => fn Vrs => {
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
          K (Local_Defs.unfold0_tac ctxt SSupp_defs),
          REPEAT_DETERM o assume_tac ctxt,
          rtac ctxt @{thm trans[OF comp_assoc]},
          rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
          rtac ctxt (#Sb_comp axioms),
          K (Local_Defs.unfold0_tac ctxt SSupp_defs),
          REPEAT_DETERM o assume_tac ctxt,
          rtac ctxt @{thm trans[OF comp_assoc[symmetric]]},
          rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
          rtac ctxt trans,
          rtac ctxt (#Map_comp (#axioms param)),
          rtac ctxt ext,
          rtac ctxt (#Map_cong (#axioms param)),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (@{thm id_o} :: maps (map #Sb_comp o axioms_of_bmv_monad) inners'),
            K (Local_Defs.unfold0_tac ctxt SSupp_defs),
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
              K (Local_Defs.unfold0_tac ctxt SSupp_defs),
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
              K (Local_Defs.unfold0_tac ctxt SSupp_defs),
              REPEAT_DETERM o assume_tac ctxt,
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms UN_extend_simps(9)}),
              rtac ctxt refl
            ]
          ]
        ])))) Vrs,
        Sb_cong = fn ctxt => EVERY1 [
          rtac ctxt @{thm comp_apply_eq},
          K (Local_Defs.unfold0_tac ctxt SSupp_defs),
          Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
            rtac ctxt @{thm trans[rotated]},
            rtac ctxt (
              let val n = length (lives_of_bmv_monad outer);
              in mk_arg_cong lthy (n + 1) Map OF (replicate n refl) end
            ),
            K (prefer_tac 2),
            rtac ctxt (#Map_cong (#axioms param)),
            K (Local_Defs.unfold0_tac ctxt (#Supp_Sb param)),
            EVERY' (map (fn Inr _ => rtac ctxt refl | Inl inner => EVERY' [
              resolve_tac ctxt (map #Sb_cong (axioms_of_bmv_monad inner)),
              K (Local_Defs.unfold0_tac ctxt SSupp_defs),
              REPEAT_DETERM1 o EVERY' [
                REPEAT_DETERM o resolve_tac ctxt (take (2 * length Injs) prems),
                FIRST' (map (fn thm => EVERY' [
                  TRY o rtac ctxt thm,
                  REPEAT_DETERM o FIRST' [
                    rtac ctxt @{thm UnI2} THEN' etac ctxt @{thm UN_I},
                    rtac ctxt @{thm UnI1}
                  ],
                  REPEAT_DETERM o etac ctxt @{thm UN_I},
                  assume_tac ctxt
                ]) (@{thm refl} :: drop (2 * length Injs) prems))
              ]
            ]) inners),
            rtac ctxt (#Sb_cong axioms),
            K (Local_Defs.unfold0_tac ctxt SSupp_defs),
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
      [leader axioms_of_bmv_monad outer']
      [the (leader params_of_bmv_monad outer')]
      [the (leader Maps_of_bmv_monad outer')]
      [new_Injs] [new_Vrs]
    } : (Proof.context -> tactic) bmv_monad_model;

    val (res, lthy) = bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Dont_Note) qualify model lthy
  in (res, lthy) end;

fun pbmv_monad_cmd (((((((b, ops), Sbs), Injs), SSupps_opt), Vrs), param_opt), bd) lthy =
  let
    val ops = map (Syntax.read_typ lthy) ops;
    val bd = Syntax.read_term lthy bd;
    val Sbs = map2 (fn Sb => fn T => Term.subst_atomic_types (
      map (apply2 TFree) (Term.add_tfreesT (body_type (fastype_of Sb)) [] ~~ Term.add_tfreesT T [])
      @ map (apply2 TFree) (Term.add_tfreesT (snd (split_last (binder_types (fastype_of Sb)))) [] ~~ Term.add_tfreesT T [])
    ) Sb) (map (Syntax.read_term lthy) Sbs) ops;
    val frees = distinct (op=) (maps (
      map (fst o dest_funT) o fst o split_last o binder_types o fastype_of
    ) Sbs);
    val Injs = map (map (Syntax.read_term lthy)) Injs;
    val _ = @{print} SSupps_opt
    val SSupps = case SSupps_opt of
      SOME SSupps => map (map (fn "_" => NONE | t => SOME (Syntax.read_term lthy t))) SSupps
      | NONE => map (map (K NONE)) Injs;
    val Vrs = map (map (map (fn "_" => NONE | t => SOME (Syntax.read_term lthy t)))) Vrs;
    val Vrs = map2 (fn T => map (map (Option.map (fn Vrs => Term.subst_atomic_types (
      map (apply2 TFree) (Term.add_tfreesT (fst (dest_funT (fastype_of Vrs))) [] ~~ Term.add_tfreesT T [])
    ) Vrs)))) ops Vrs;

    val b = if Binding.is_empty b then fst (dest_Type (hd ops)) else Local_Theory.full_name lthy b

    val vars = distinct (op=) (map TFree (fold Term.add_tfreesT ops []));

    val names_lthy = lthy
      |> fold Variable.declare_typ vars

    val (lives, lives', param_consts) = case param_opt of
      NONE => ([], [], replicate (length ops) NONE)
      | SOME (Maps, Suppss) =>
        let
          val Maps = map (fn "_" => NONE | s => SOME (Syntax.read_term lthy s)) Maps;
          val Suppss = map (fn [] => NONE | xs => SOME (map (Syntax.read_term lthy) xs)) Suppss;

          val lives = the_default [] (Option.map (fn Map =>
            let
              val Map = Term.subst_atomic_types (map (apply2 TFree) (
                Term.add_tfreesT (snd (split_last (binder_types (fastype_of Map)))) []
                ~~ Term.add_tfreesT (hd ops) []
              )) Map;
            in map (fst o dest_funT) (fst (split_last (binder_types (fastype_of Map)))) end
          ) (hd Maps));
          val (lives', _) = names_lthy
            |> mk_TFrees' (map Type.sort_of_atyp lives);

          val Maps = map2 (fn T => Option.map (fn Map =>
            let
              val l' = map (snd o dest_funT) (fst (split_last (binder_types (fastype_of Map))));
              val TA = snd (split_last (binder_types (fastype_of Map)));
              val Map = Term.subst_atomic_types (map (apply2 TFree) (
                Term.add_tfreesT TA [] ~~ Term.add_tfreesT T []
              )) Map;
              val TA = snd (split_last (binder_types (fastype_of Map)));
              val TB = body_type (fastype_of Map);
              val old_vars = map TFree (Term.add_tfreesT TB []);
            in Term.subst_atomic_types (
              (l' ~~ lives') @ (
                subtract (op=) l' old_vars ~~ subtract (op=) lives (map TFree (Term.add_tfreesT TA []))
              )
            ) Map end
          )) ops (Maps @ replicate (length ops - length Maps) NONE);

          val Suppss = map2 (fn T => Option.map (map (fn Supp => Term.subst_atomic_types (map (apply2 TFree) (
            Term.add_tfreesT (hd (binder_types (fastype_of Supp))) [] ~~ Term.add_tfreesT T []
          )) Supp))) ops (Suppss @ replicate (length ops - length Suppss) NONE);

        in (lives, lives',
          map2 (@{map_option 2} (fn Map => fn Supps => { Map = Map, Supps = Supps })) Maps Suppss
        ) end;

    val consts = {
      bd = bd,
      Injs = Injs,
      SSupps = SSupps,
      Sbs = Sbs,
      Vrs = Vrs,
      params = param_consts
    }: (term option) bmv_monad_consts;
    val (consts, bmv_defs, SSupp_defs, lthy) = define_bmv_monad_consts BNF_Def.Smart_Inline BNF_Def.Dont_Note I 0
      ops lives' consts lthy;

    val param_goals = @{map 5} (fn Sb => fn Injs => fn SSupps => fn Vrs => Option.map (fn { Map, Supps } =>
      mk_param_axiom Map Supps SSupps Sb Injs Vrs bd lthy
    )) Sbs Injs (#SSupps consts) Vrs (#params consts);

    val (goals, SSupp_eq_goals) = mk_bmv_monad_axioms ops consts SSupp_defs [] lthy;

    fun after_qed thmss lthy =
      let
        val thms = map hd thmss;
        val bd_irco = hd thms;

        val chop_many = fold_map (
          fn NONE => (fn thms => (NONE, thms))
          | SOME _ => fn thms => (SOME (hd thms), tl thms)
        );

        val (((axioms, SSupp_eq), params), _) = apfst (apfst split_list o split_list) (@{fold_map 4} (fn goal => fn SSupp_eq_goals => fn param => fn param_consts => fn thms =>
          let
            val ((((((((Sb_Inj, Sb_comp_Injs), SSupp_eq), Sb_comp), Vrs_bds), Vrs_Injs), Vrs_Sbs), Sb_cong), thms) = thms
              |> apfst hd o chop 1
              ||>> chop (length (#Sb_comp_Injs goal))
              ||>> chop_many SSupp_eq_goals
              ||>> apfst hd o chop 1
              ||>> fold_map chop_many (#Vrs_bds goal)
              ||>> fold_map chop_many (#Vrs_Injs goal)
              ||>> fold_map chop_many (#Vrs_Sbs goal)
              ||>> apfst hd o chop 1;
            val (param, thms) = case param of NONE => (NONE, thms) | SOME goals =>
              let val ((((((((Map_id, Map_comp), Supp_maps), Supp_bds), Map_cong), Map_Sb), Supp_Sb), Map_Vrs), thms) = thms
                |> apfst hd o chop 1
                ||>> apfst hd o chop 1
                ||>> chop (length (#Supps (the param_consts)))
                ||>> chop (length (#Supps (the param_consts)))
                ||>> apfst hd o chop 1
                ||>> apfst hd o chop 1
                ||>> chop (length (#Supps (the param_consts)))
                ||>> fold_map chop_many (#Map_Vrs goals)
              in (SOME ({
                axioms = {
                  Map_id = Map_id,
                  Map_comp = Map_comp,
                  Supp_Map = Supp_maps,
                  Supp_bd = Supp_bds,
                  Map_cong = Map_cong
                },
                Map_Sb = Map_Sb,
                Supp_Sb = Supp_Sb,
                Map_Vrs = Map_Vrs
              } : thm bmv_monad_param), thms) end;
          in ((({
            Sb_Inj = Sb_Inj,
            Sb_comp_Injs = Sb_comp_Injs,
            Sb_comp = Sb_comp,
            Vrs_bds = Vrs_bds,
            Vrs_Injs = Vrs_Injs,
            Vrs_Sbs = Vrs_Sbs,
            Sb_cong = Sb_cong
          }: thm bmv_monad_axioms, SSupp_eq), param), thms) end
        ) goals SSupp_eq_goals param_goals param_consts (tl thms));

        val model = {
          ops = ops,
          var_class = @{class var}, (* TODO: change *)
          leader = 0,
          frees = frees,
          lives = lives,
          lives' = lives',
          deads = subtract (op=) (lives @ frees) vars,
          bmv_ops = [],
          consts = consts,
          params = params,
          bd_infinite_regular_card_order = bd_irco,
          SSupp_eq = SSupp_eq,
          tacs = axioms
        } : thm bmv_monad_model;

        val (bmv, lthy) = mk_bmv_monad BNF_Def.Smart_Inline (K BNF_Def.Note_Some) SSupp_defs model lthy;

        val lthy = register_pbmv_monad b bmv lthy;
      in lthy end;
  in Proof.theorem NONE after_qed (map (single o rpair []) (
    [HOLogic.mk_Trueprop (mk_infinite_regular_card_order bd)]
    @ flat (@{map 3} (fn goal => fn SSupp_eq_goals => fn param => #Sb_Inj goal :: #Sb_comp_Injs goal @ map_filter I SSupp_eq_goals @ [#Sb_comp goal]
      @ maps (map_filter I) (#Vrs_bds goal @ #Vrs_Injs goal @ #Vrs_Sbs goal)
      @ [#Sb_cong goal] @ the_default [] (Option.map (fn param =>
        [#Map_id (#axioms param), #Map_comp (#axioms param)] @ #Supp_Map (#axioms param)
        @ #Supp_bd (#axioms param) @ [#Map_cong (#axioms param), #Map_Sb param]
        @ #Supp_Sb param @ maps (map_filter I) (#Map_Vrs param)
      ) param)
    ) goals SSupp_eq_goals param_goals)
  )) lthy
    |> Proof.unfolding ([[(bmv_defs, [])]])
    |> Proof.refine_singleton (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (TRYALL (rtac ctxt refl))))
  end;

fun print_pbmv_monads ctxt =
  let
    val and_list = Library.separate (Pretty.block [Pretty.brk 1, Pretty.keyword2 "and", Pretty.brk 1])
    fun map_filter_end [] _ = []
      | map_filter_end (SOME x::xs) ys = ys @ [SOME x] @ map_filter_end xs ys
      | map_filter_end (NONE::xs) ys = map_filter_end xs (NONE::ys)
    fun pretty_mrbnf (key, bmv as BMV {ops, frees, lives, consts, ...}) =
      Pretty.big_list
        (Pretty.string_of (Pretty.block ([Pretty.str key, Pretty.str ":", Pretty.brk 1] @
          and_list (map (Pretty.quote o Syntax.pretty_typ ctxt) ops))))
        ([Pretty.block [Pretty.str "frees:", Pretty.brk 1, Pretty.str (string_of_int (length frees)),
            Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) frees)]] @
          (if length lives > 0 then
            [Pretty.block [Pretty.str "live:", Pretty.brk 1, Pretty.str (string_of_int (length lives)),
              Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) lives)]]
          else []) @
          [ Pretty.block ([Pretty.str "Sb:", Pretty.brk 1] @ and_list (map (Pretty.quote o Syntax.pretty_term ctxt) (#Sbs consts)))
          ] @ (case map_filter I (Maps_of_bmv_monad bmv) of [] => [] | _ => [
            Pretty.block ([Pretty.str "Map:", Pretty.brk 1] @ and_list (map (fn x => case x of
              NONE => Pretty.str "_" | SOME y => Pretty.quote (Syntax.pretty_term ctxt y)) (
                map_filter_end (Maps_of_bmv_monad bmv) []
              )))
          ]) @ [Pretty.block [Pretty.str ("bd:"), Pretty.brk 1,
            Pretty.quote (Syntax.pretty_term ctxt (#bd consts))]]);
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
  (parse_opt_binding_colon -- Parse.and_list1 Parse.typ --|
    (Parse.reserved "Sbs" -- @{keyword ":"}) -- Parse.and_list1 Parse.term --|
    (Parse.reserved "Injs" -- @{keyword ":"}) -- Parse.and_list1 (Scan.repeat1 (Scan.unless (Parse.reserved "Vrs" || Parse.reserved "SSupps") Parse.term)) --
    (Scan.option ((Parse.reserved "SSupps" -- @{keyword ":"}) |-- Parse.and_list1 (Scan.repeat1 (Scan.unless (Parse.reserved "Vrs") (Parse.underscore || Parse.term))))) --|
    (Parse.reserved "Vrs" -- @{keyword ":"}) -- Parse.and_list1 (Parse.list1 (
      Scan.repeat1 (Scan.unless (Parse.reserved "Map" || Parse.reserved "bd") (Parse.underscore || Parse.term))
    )) --
    Scan.optional (
      (Parse.reserved "Map" -- @{keyword ":"}) |-- Parse.and_list1 (Parse.underscore || Parse.term) --|
      (Parse.reserved "Supps" -- @{keyword ":"}) -- Parse.and_list1 (
        Scan.repeat1 (Scan.unless (Parse.reserved "bd") Parse.term)
        || (Parse.underscore >> K [])
      )
      >> SOME
    ) NONE --|
    (Parse.reserved "bd" -- @{keyword ":"}) -- Parse.term
  >> pbmv_monad_cmd)

end