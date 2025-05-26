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
    Vrs_bds: 'a list,
    Vrs_Injss: 'a list list,
    Vrs_Sbs: 'a list
  };

  type bmv_monad_facts = {
    Inj_inj: thm list,
    Supp_Injss: thm list list,
    SSupp_Map_subsets: thm list option,
    SSupp_Map_bounds: thm list option,
    SSupp_Sb_subsets: thm list,
    SSupp_Sb_bounds: thm list
  };

  type bmv_monad_consts = {
    bd: term,
    Sbs: term list,
    RVrs: term list list,
    Injs: term list list,
    Vrs: term list list,
    params: { Map: term, Supps: term list } option list
  };

  type 'a bmv_monad_param = {
    axioms: 'a supported_functor_axioms,
    Map_Sb: 'a,
    Supp_Sb: 'a list,
    Vrs_Map: 'a list,
    Map_Injs: 'a list
  };

  type 'a bmv_monad_model = {
    ops: typ list,
    var_class: class,
    bmv_ops: bmv_monad list,
    frees: typ list list,
    deads: typ list list,
    leader: int,
    lives: typ list list,
    lives': typ list list,
    consts: bmv_monad_consts,
    params: 'a bmv_monad_param option list,
    bd_infinite_regular_card_order: 'a,
    tacs: 'a bmv_monad_axioms list
  }

  val ops_of_bmv_monad: bmv_monad -> typ list;
  val bd_of_bmv_monad: bmv_monad -> term;
  val bd_infinite_regular_card_order_of_bmv_monad: bmv_monad -> thm;
  val var_class_of_bmv_monad: bmv_monad -> class;
  val leader_of_bmv_monad: bmv_monad -> int;
  val frees_of_bmv_monad: bmv_monad -> typ list list;
  val lives_of_bmv_monad: bmv_monad -> typ list list;
  val lives'_of_bmv_monad: bmv_monad -> typ list list;
  val deads_of_bmv_monad: bmv_monad -> typ list list;
  val Injs_of_bmv_monad: bmv_monad -> term list list;
  val Sbs_of_bmv_monad: bmv_monad -> term list;
  val Maps_of_bmv_monad: bmv_monad -> term option list;
  val Supps_of_bmv_monad: bmv_monad -> term list option list;
  val Vrs_of_bmv_monad: bmv_monad -> term list list;
  val RVrs_of_bmv_monad: bmv_monad -> term list list;
  val axioms_of_bmv_monad: bmv_monad -> thm bmv_monad_axioms list;
  val facts_of_bmv_monad: bmv_monad -> bmv_monad_facts list;
  val params_of_bmv_monad: bmv_monad -> thm bmv_monad_param option list;

  val map_bmv_monad_axioms: ('a -> 'b) -> 'a bmv_monad_axioms -> 'b bmv_monad_axioms;
  val apply_bmv_monad_axioms: ('a -> 'b) bmv_monad_axioms -> 'a bmv_monad_axioms -> 'b bmv_monad_axioms;
  val morph_bmv_monad: morphism -> bmv_monad -> bmv_monad;

  val register_pbmv_monad: string -> bmv_monad -> local_theory -> local_theory;
  val pbmv_monad_of_generic: Context.generic -> string -> bmv_monad option;
  val pbmv_monad_of: Proof.context -> string -> bmv_monad option;

  val pbmv_monad_of_mrbnf: MRBNF_Def.mrbnf -> local_theory -> bmv_monad * local_theory
  val register_mrbnf_as_pbmv_monad: string -> local_theory -> local_theory
  val note_bmv_monad_thms: (Proof.context -> BNF_Def.fact_policy) -> (binding -> binding)
    -> binding option -> bmv_monad -> local_theory -> (string * thm list) list * local_theory
  val bmv_monad_def: BNF_Def.inline_policy -> (Proof.context -> BNF_Def.fact_policy)
    -> (binding -> binding) -> binding option -> (Proof.context -> tactic) bmv_monad_model -> local_theory -> (bmv_monad * thm list) * local_theory

  val compose_bmv_monad: (binding -> binding) -> bmv_monad -> (bmv_monad, typ) MRBNF_Util.either list
    -> { frees: typ list, deads: typ list }
    -> { frees: typ list, deads: typ list, lives: typ list } option list -> local_theory
    -> (bmv_monad * thm list) * local_theory
end

structure BMV_Monad_Def : BMV_MONAD_DEF = struct

open MRBNF_Util

type 'a bmv_monad_axioms = {
  Sb_Inj: 'a,
  Sb_comp_Injs: 'a list,
  Sb_comp: 'a,
  Sb_cong: 'a,
  Vrs_bds: 'a list,
  Vrs_Injss: 'a list list,
  Vrs_Sbs: 'a list
};

fun map_bmv_monad_axioms f ({
  Sb_Inj, Sb_comp_Injs, Sb_comp, Sb_cong, Vrs_bds, Vrs_Injss, Vrs_Sbs
}: 'a bmv_monad_axioms) = {
  Sb_Inj = f Sb_Inj,
  Sb_comp_Injs = map f Sb_comp_Injs,
  Sb_comp = f Sb_comp,
  Sb_cong = f Sb_cong,
  Vrs_bds = map f Vrs_bds,
  Vrs_Injss = map (map f) Vrs_Injss,
  Vrs_Sbs = map  f Vrs_Sbs
} : 'b bmv_monad_axioms;

val morph_bmv_monad_axioms = map_bmv_monad_axioms o Morphism.thm;

fun apply_bmv_monad_axioms ({
  Sb_Inj=f1, Sb_comp_Injs=f2s, Sb_comp=f3, Sb_cong=f4, Vrs_bds=f5s, Vrs_Injss=f6s, Vrs_Sbs=f7s
}: ('a -> 'b) bmv_monad_axioms) ({
  Sb_Inj, Sb_comp_Injs, Sb_comp, Sb_cong, Vrs_bds, Vrs_Injss, Vrs_Sbs
}: 'a bmv_monad_axioms) = {
  Sb_Inj = f1 Sb_Inj,
  Sb_comp_Injs = map2 (curry (op|>)) Sb_comp_Injs f2s,
  Sb_comp = f3 Sb_comp,
  Sb_cong = f4 Sb_cong,
  Vrs_bds = map2 (curry (op|>)) Vrs_bds f5s,
  Vrs_Injss = map2 (map2 (curry (op|>))) Vrs_Injss f6s,
  Vrs_Sbs = map2 (curry (op|>)) Vrs_Sbs f7s
} : 'b bmv_monad_axioms;

type bmv_monad_facts = {
  Inj_inj: thm list,
  Supp_Injss: thm list list,
  SSupp_Map_subsets: thm list option,
  SSupp_Map_bounds: thm list option,
  SSupp_Sb_subsets: thm list,
  SSupp_Sb_bounds: thm list
};

fun morph_bmv_monad_facts phi { Inj_inj, Supp_Injss, SSupp_Map_subsets, SSupp_Map_bounds, SSupp_Sb_subsets, SSupp_Sb_bounds } = {
  Inj_inj = map (Morphism.thm phi) Inj_inj,
  Supp_Injss = map (map (Morphism.thm phi)) Supp_Injss,
  SSupp_Map_subsets = Option.map (map (Morphism.thm phi)) SSupp_Map_subsets,
  SSupp_Map_bounds = Option.map (map (Morphism.thm phi)) SSupp_Map_bounds,
  SSupp_Sb_subsets = map (Morphism.thm phi) SSupp_Sb_subsets,
  SSupp_Sb_bounds = map (Morphism.thm phi) SSupp_Sb_bounds
}: bmv_monad_facts;

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
  Vrs_Map: 'a list,
  Map_Injs: 'a list
};

fun map_bmv_monad_param f ({ axioms, Map_Sb, Supp_Sb, Vrs_Map, Map_Injs }: 'a bmv_monad_param) = {
  axioms = map_supported_functor_axioms f axioms,
  Map_Sb = f Map_Sb,
  Supp_Sb = map f Supp_Sb,
  Vrs_Map = map f Vrs_Map,
  Map_Injs = map f Map_Injs
}: 'b bmv_monad_param;


type bmv_monad_consts = {
  bd: term,
  Sbs: term list,
  RVrs: term list list,
  Injs: term list list,
  Vrs: term list list,
  params: { Map: term, Supps: term list} option list
};

fun morph_bmv_monad_consts phi { bd, params, Injs, Sbs, Vrs, RVrs } = {
  bd = Morphism.term phi bd,
  RVrs = map (map (Morphism.term phi)) RVrs,
  params = map (Option.map (fn { Map, Supps } => {
    Map = Morphism.term phi Map,
    Supps = map (Morphism.term phi) Supps
  })) params,
  Injs = map (map (Morphism.term phi)) Injs,
  Sbs = map (Morphism.term phi) Sbs,
  Vrs = map (map (Morphism.term phi)) Vrs
}: bmv_monad_consts;

datatype bmv_monad = BMV of {
  ops: typ list,
  var_class: class,
  leader: int,
  frees: typ list list,
  lives: typ list list,
  lives': typ list list,
  deads: typ list list,
  consts: bmv_monad_consts,
  params: thm bmv_monad_param option list,
  bd_infinite_regular_card_order: thm,
  axioms: thm bmv_monad_axioms list,
  facts: bmv_monad_facts list
}

fun morph_bmv_monad phi (BMV {
  ops, var_class, leader, frees, lives, lives', deads, consts, params, axioms, bd_infinite_regular_card_order,
  facts
}) = BMV {
  ops = map (Morphism.typ phi) ops,
  leader = leader,
  var_class = var_class,
  frees = map (map (Morphism.typ phi)) frees,
  lives = map (map (Morphism.typ phi)) lives,
  lives' = map (map (Morphism.typ phi)) lives',
  deads = map (map (Morphism.typ phi)) deads,
  consts = morph_bmv_monad_consts phi consts,
  params = map (Option.map (map_bmv_monad_param (Morphism.thm phi))) params,
  axioms = map (morph_bmv_monad_axioms phi) axioms,
  facts = map (morph_bmv_monad_facts phi) facts,
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
val Sbs_of_bmv_monad = #Sbs o #consts o Rep_bmv
val Maps_of_bmv_monad = map (Option.map #Map) o #params o #consts o Rep_bmv
val Supps_of_bmv_monad = map (Option.map #Supps) o #params o #consts o Rep_bmv
val Vrs_of_bmv_monad = #Vrs o #consts o Rep_bmv
val RVrs_of_bmv_monad = #RVrs o #consts o Rep_bmv
val consts_of_bmv_monad = #consts o Rep_bmv
val axioms_of_bmv_monad = #axioms o Rep_bmv
val facts_of_bmv_monad = #facts o Rep_bmv
val params_of_bmv_monad = #params o Rep_bmv
val bd_infinite_regular_card_order_of_bmv_monad = #bd_infinite_regular_card_order o Rep_bmv

type 'a bmv_monad_model = {
  ops: typ list,
  var_class: class,
  frees: typ list list,
  lives: typ list list,
  lives': typ list list,
  deads: typ list list,
  consts: bmv_monad_consts,
  params: 'a bmv_monad_param option list,
  bmv_ops: bmv_monad list,
  leader: int,
  bd_infinite_regular_card_order: 'a,
  tacs: 'a bmv_monad_axioms list
}

fun morph_bmv_monad_model phi f ({ ops, var_class, frees, lives, lives', consts, bmv_ops, leader,
  params, tacs, bd_infinite_regular_card_order, deads }
) = {
  ops = map (Morphism.typ phi) ops,
  var_class = var_class,
  frees = map (map (Morphism.typ phi)) frees,
  lives = map (map (Morphism.typ phi)) lives,
  lives' = map (map (Morphism.typ phi)) lives',
  deads = map (map (Morphism.typ phi)) deads,
  consts = morph_bmv_monad_consts phi consts,
  params = params,
  bmv_ops = map (morph_bmv_monad phi) bmv_ops,
  leader = leader,
  tacs = map (map_bmv_monad_axioms f) tacs,
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

fun mk_small_prems fs rhos Injs = map (HOLogic.mk_Trueprop o mk_supp_bound) fs
  @ map2 (fn rho => fn Inj => HOLogic.mk_Trueprop (mk_ordLess
  (mk_card_of (MRBNF_Util.mk_SSupp Inj $ rho))
  (mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of rho))))
)) rhos Injs;

fun mk_bmv_monad_axioms ops consts bmv_ops lthy =
  let
    val Ts = ops @ maps ops_of_bmv_monad bmv_ops;
    val Sbs = #Sbs consts @ maps Sbs_of_bmv_monad bmv_ops;
    val Injss = #Injs consts @ maps Injs_of_bmv_monad bmv_ops;
    val RVrss = #RVrs consts @ maps RVrs_of_bmv_monad bmv_ops;
    val Vrss = #Vrs consts @ maps Vrs_of_bmv_monad bmv_ops;

    val axioms = @{map 5} (fn T => fn Injs => fn Sb => fn (Vrs: term list) => fn (RVrs: term list) =>
      let
        val (own_Injs, other_Injs) = partition (fn Inj => body_type (fastype_of Inj) = T) Injs;
        val other_idxs = map (fn Inj => find_index (fn T => body_type (fastype_of Inj) = T) Ts) other_Injs;

        val f_Ts = filter ((op=) o dest_funT) (fst (split_last (binder_types (fastype_of Sb))));

        val ((((((fs, gs), rhos), rhos'), aa), x), _) = lthy
          |> mk_Frees "f" f_Ts
          ||>> mk_Frees "g" f_Ts
          ||>> mk_Frees "\<rho>" (map fastype_of Injs)
          ||>> mk_Frees "\<rho>'" (map fastype_of Injs)
          ||>> mk_Frees "a" (distinct (op=) (map (fst o dest_funT o fastype_of) Injs @ map (fst o dest_funT) f_Ts))
          ||>> apfst hd o mk_Frees "x" [T];
        val (own_rhos, other_rhos) = partition (curry (op=) T o body_type o fastype_of) rhos;

        val f_ids = map (HOLogic.id_const o fst o dest_funT o fastype_of) fs;

        val Sb_Inj = mk_Trueprop_eq (Term.list_comb (Sb, f_ids @ Injs), HOLogic.id_const T);

        val small_prems = mk_small_prems fs rhos Injs;
        val small_prems' = mk_small_prems gs rhos' Injs;

        val Sb_comp_Injs = map2 (fn Inj => fn rho =>
          fold_rev Logic.all (fs @ rhos) (fold_rev (curry Logic.mk_implies) small_prems (mk_Trueprop_eq (
            HOLogic.mk_comp (Term.list_comb (Sb, fs @ rhos), Inj), rho
          )))
        ) own_Injs own_rhos;

        val Sb_comp = fold_rev Logic.all (gs @ rhos' @ fs @ rhos) (
          fold_rev (curry Logic.mk_implies) (small_prems @ small_prems') (mk_Trueprop_eq (
            HOLogic.mk_comp (Term.list_comb (Sb, gs @ rhos'), Term.list_comb (Sb, fs @ rhos)),
            Term.list_comb (Sb, map2 (curry HOLogic.mk_comp) gs fs @ 
              fst (fold_map (fn rho => fn acc as (Sbs, Injs, RVrs) => if member (op=) own_rhos rho then
                (HOLogic.mk_comp (
                  Term.list_comb (Sb, gs @ rhos'), rho
                ), acc)
              else
                (HOLogic.mk_comp (Term.list_comb (hd Sbs, map (fn RVr => 
                  the (List.find (curry (op=) (HOLogic.dest_setT (body_type (fastype_of RVr))) o domain_type o fastype_of) gs)
                ) (hd RVrs) @ map (fn Inj =>
                  case List.find (fn rho' => fastype_of rho' = fastype_of Inj) rhos' of
                    NONE => Inj | SOME t => t
                ) (hd Injs)), rho), (tl Sbs, tl Injs, tl RVrs))
            ) rhos (map (nth Sbs) other_idxs, map (nth Injss) other_idxs, map (nth RVrss) other_idxs)))
          ))
        );

        val Vrs_bds = map (fn Vrs => Logic.all x (
          HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (Vrs $ x)) (#bd consts))
        )) (RVrs @ Vrs);

        val Vrs_Injss = map2 (fn Inj' => fn Vrs => map (fn Inj =>
          let
            val a = the (List.find (fn a => fastype_of a = hd (binder_types (fastype_of Inj))) aa);
            val T = HOLogic.dest_setT (body_type (fastype_of Vrs));
          in Logic.all a (mk_Trueprop_eq (
            Vrs $ (Inj $ a),
            if Inj' = Inj then mk_singleton a else mk_bot T))
          end
        ) own_Injs) Injs Vrs;

        val Vrs_Sbs = map2 (fn f => fn RVr =>
          fold_rev Logic.all (fs @ rhos @ [x]) (
            fold_rev (curry Logic.mk_implies) small_prems (mk_Trueprop_eq (
              RVr $ (Term.list_comb (Sb, fs @ rhos) $ x), mk_image f $ (RVr $ x)
            ))
          )
        ) fs RVrs @ map2 (fn Vr => fn Inj => 
          let
            val UNs = @{map_filter 2} (fn Vr' => fn rho =>
              if body_type (fastype_of rho) <> body_type (fastype_of Inj) then NONE else
              let
                val X = Vr' $ x
                val inner_Vr = if body_type (fastype_of rho) = domain_type (fastype_of Vr) then Vr else
                  let
                    val idx = find_index (curry (op=) (body_type (fastype_of rho))) Ts;
                    val Vrs = nth Vrss idx;
                    val Inj_idx = find_index (curry (op=) Inj) (nth Injss idx);
                  in nth Vrs Inj_idx end
              in SOME (
                mk_UNION (Vr' $ x) (Term.abs ("x", HOLogic.dest_setT (fastype_of X)) (
                  inner_Vr $ (rho $ Bound 0)
                ))
              ) end
            ) Vrs rhos;
          in fold_rev Logic.all (fs @ rhos @ [x]) (
            fold_rev (curry Logic.mk_implies) small_prems (mk_Trueprop_eq (
              Vr $ (Term.list_comb (Sb, fs @ rhos) $ x), foldl1 mk_Un UNs
            ))
          ) end
        ) Vrs Injs;

        val Sb_cong = fold_rev Logic.all (fs @ rhos @ gs @ rhos' @ [x]) (
          fold_rev (curry Logic.mk_implies) (small_prems @ small_prems' @ @{map 3} (fn rho => fn rho' => fn Vrs =>
            let val a = the (List.find (fn t => fastype_of t = HOLogic.dest_setT (body_type (fastype_of Vrs))) aa)
            in Logic.all a (Logic.mk_implies (
              HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Vrs $ x)),
              mk_Trueprop_eq (rho $ a, rho' $ a)
            )) end
          ) (fs @ rhos) (gs @ rhos') (RVrs @ Vrs)) (mk_Trueprop_eq (
            Term.list_comb (Sb, fs @ rhos) $ x,
            Term.list_comb (Sb, gs @ rhos') $ x
          )
        ));
      in {
        Sb_Inj = Sb_Inj,
        Sb_comp_Injs = Sb_comp_Injs,
        Sb_comp = Sb_comp,
        Vrs_Injss = Vrs_Injss,
        Vrs_bds = Vrs_bds,
        Vrs_Sbs = Vrs_Sbs,
        Sb_cong = Sb_cong
      } : term bmv_monad_axioms end
    ) ops (#Injs consts) (#Sbs consts) (#Vrs consts) (#RVrs consts);
  in axioms end;

fun mk_param_axiom Map Supps Sb Injs RVrs Vrs bd params lthy =
  let
    val (f_Ts, T) = split_last (binder_types (fastype_of Map));
    val (lives, lives') = split_list (map dest_funT f_Ts);

    val h_Ts = filter ((op=) o dest_funT) (fst (split_last (binder_types (fastype_of Sb))));

    val (Cs, _) = lthy
      |> mk_TFrees (length lives);
    val (((((fs, gs), hs), rhos), x), _) = lthy
      |> mk_Frees "f" (map2 (curry (op-->)) lives lives')
      ||>> mk_Frees "g" (map2 (curry (op-->)) lives' Cs)
      ||>> mk_Frees "f" h_Ts
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

    val Map_Sb = fold_rev Logic.all (fs @ hs @ rhos) (
      fold_rev (curry Logic.mk_implies) (mk_small_prems hs rhos Injs) (mk_Trueprop_eq (
        HOLogic.mk_comp (Term.list_comb (Map, fs), Term.list_comb (Sb, hs @ rhos)),
        HOLogic.mk_comp (Term.list_comb (
          Term.subst_atomic_types (lives ~~ lives') Sb, hs @ map (fn rho =>
            case List.find (fn { Map, ...} => snd (split_last (binder_types (fastype_of Map))) = body_type (fastype_of rho)) params of
              NONE => rho | SOME { Map, ... } =>
                let
                  val (lives, lives') = split_list (map dest_funT (fst (split_last (binder_types (fastype_of Map)))));
                  val fs = map (fn l => the_default (HOLogic.id_const l) (List.find (curry (op=) l o domain_type o fastype_of) fs)) lives;
                  val subst = @{map 3} (fn l => fn l' => fn f => if (op=) (dest_funT (fastype_of f)) then
                    (l', l) else (l', body_type (fastype_of f))
                  ) lives lives' fs;
                in HOLogic.mk_comp (Term.list_comb (Term.subst_atomic_types subst Map, fs), rho) end
          ) rhos
        ), Term.list_comb (Map, fs))
      ))
    );

    val Vrs_Map = map (fn Vrs =>
      fold_rev Logic.all (fs @ [x]) (mk_Trueprop_eq (
        Term.subst_atomic_types (lives ~~ lives') Vrs $ (Term.list_comb (Map, fs) $ x),
        Vrs $ x
      ))
    ) (RVrs @ Vrs);

    val Supp_Sb = map (fn Supp => fold_rev Logic.all (rhos @ hs @ [x]) (
      fold_rev (curry Logic.mk_implies) (mk_small_prems hs rhos Injs) (mk_Trueprop_eq (
        Supp $ (Term.list_comb (Sb, hs @ rhos) $ x), Supp $ x
      ))
    )) Supps;

    val Map_Injs = map_filter (fn Inj => if body_type (fastype_of Inj) <> T then NONE else SOME (
      fold_rev Logic.all fs (mk_Trueprop_eq (
        HOLogic.mk_comp (Term.list_comb (Map, fs), Inj),
        Term.subst_atomic_types (lives ~~ lives') Inj
      ))
    )) Injs;
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
    Vrs_Map = Vrs_Map,
    Map_Injs = Map_Injs
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

fun define_bmv_monad_consts const_policy fact_policy qualify leader ops lives' (consts: bmv_monad_consts) lthy =
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

    val (RVrs', lthy) = (@{fold_map 3} (fn suffix => fn Sb => @{fold_map 2} (fn j => fn Vrs =>
      maybe_define' (Binding.suffix_name ("_" ^ string_of_int j) (suffix (Binding.name "RVrs"))) Vrs
    ) (1 upto length (filter ((op=) o dest_funT) (fst (split_last (binder_types (fastype_of Sb))))))) suffixes Sbs (#RVrs consts) lthy); 

    val (Vrs', lthy) = (@{fold_map 2} (@{fold_map 2} (fn suffix => fn Vrs =>
      maybe_define' (suffix (Binding.name "Vrs")) Vrs
    )) suffixess (#Vrs consts) lthy);

    val Vrs = map (map fst) Vrs';
    val Vrs_defs = maps (map snd) Vrs';

    val RVrs = map (map fst) RVrs';
    val RVrs_defs = maps (map snd) RVrs';

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
      Sbs = Sbs,
      RVrs = RVrs,
      Vrs = Vrs
    } : bmv_monad_consts;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val vars = map TFree (rev (Term.add_tfreesT (nth ops leader) [])) @ flat lives';
    val subst = (map (Morphism.typ phi) vars ~~ vars);

    val phi' = Morphism.term_morphism "bmv_monad_export" (Term.subst_atomic_types subst o Morphism.term phi)
    val consts' = morph_bmv_monad_consts phi' consts';

    val defs = map_filter I (Sb_defs @ flat Inj_defs @ Vrs_defs @ RVrs_defs @ [bd_def] @ flat param_defs);
  in (consts', map (Morphism.thm phi) defs, lthy) end;

fun note_bmv_monad_thms fact_policy qualify bmv_b_opt bmv lthy =
  let
    fun bmv_b () = case bmv_b_opt of
      NONE => Binding.name (short_type_name (fst (dest_Type (nth (ops_of_bmv_monad bmv) (leader_of_bmv_monad bmv)))))
      | SOME b => b;
    fun tl_maybe (_::x::xs) = x::xs
      | tl_maybe xs = xs

    fun bmv_name () = implode (tl (maps (fn x => [".", x]) (tl_maybe (String.tokens (fn c => c = #".") (Binding.name_of (bmv_b ()))))));
    val axioms = axioms_of_bmv_monad bmv;
    val facts = facts_of_bmv_monad bmv;
    val params = params_of_bmv_monad bmv;

    fun note_unless_dont_note (noted, lthy) =
      let val notes =
        [
         ("Sb_Inj", map #Sb_Inj axioms, []),
         ("Sb_comp_Inj", maps #Sb_comp_Injs axioms, []),
         ("Sb_comp", map #Sb_comp axioms, []),
         ("Sb_cong", map #Sb_cong axioms, []),
         ("Vrs_bd", maps #Vrs_bds axioms, []),
         ("Vrs_Inj", flat (maps #Vrs_Injss axioms), []),
         ("Vrs_Sb", maps #Vrs_Sbs axioms, []),
         ("Map_Sb", map_filter (Option.map #Map_Sb) params, []),
         ("Vrs_Map", flat (map_filter (Option.map #Vrs_Map) params), []),
         ("Map_Inj", flat (map_filter (Option.map #Map_Injs) params), []),
         ("Map_id", map_filter (Option.map (#Map_id o #axioms)) params, []),
         ("Map_comp", map_filter (Option.map (#Map_comp o #axioms)) params, []),
         ("Map_cong", map_filter (Option.map (#Map_cong o #axioms)) params, []),
         ("Supp_Sb", flat (map_filter (Option.map #Supp_Sb) params), []),
         ("Supp_Map", flat (map_filter (Option.map (#Supp_Map o #axioms)) params), []),
         ("Supp_bd", flat (map_filter (Option.map (#Supp_bd o #axioms)) params), []),
         ("Inj_inj", maps #Inj_inj facts, []),
         ("Supp_Inj", flat (maps #Supp_Injss facts), []),
         ("SSupp_Map_subset", maps (the_default [] o #SSupp_Map_subsets) facts, []),
         ("SSupp_Map_bound", maps (the_default [] o #SSupp_Map_bounds) facts, []),
         ("SSupp_Sb_subset", maps #SSupp_Sb_subsets facts, []),
         ("SSupp_Sb_bound", maps #SSupp_Sb_bounds facts, [])
        ]
        |> filter_out (null o #2)
        |> map (fn (thmN, thms, attrs) => ((qualify (Binding.qualify true (bmv_name ()) (Binding.name thmN)), attrs), [(thms, [])]));
      in Local_Theory.notes notes lthy |>> append noted end
    val fact_policy = fact_policy lthy;
  in ([], lthy)
    |> fact_policy <> BNF_Def.Dont_Note ? note_unless_dont_note
  end

fun mk_bmv_monad const_policy fact_policy qualify bmv_b_opt (model: thm bmv_monad_model) lthy =
  let
    val consts = {
      bd = #bd (#consts model),
      params = #params (#consts model) @ maps (#params o #consts o Rep_bmv) (#bmv_ops model),
      Injs = #Injs (#consts model) @ maps (#Injs o #consts o Rep_bmv) (#bmv_ops model),
      Sbs = #Sbs (#consts model) @ maps (#Sbs o #consts o Rep_bmv) (#bmv_ops model),
      Vrs = #Vrs (#consts model) @ maps (#Vrs o #consts o Rep_bmv) (#bmv_ops model),
      RVrs = #RVrs (#consts model) @ maps (#RVrs o #consts o Rep_bmv) (#bmv_ops model)
    }: bmv_monad_consts;
    val axioms = #tacs model @ maps (#axioms o Rep_bmv) (#bmv_ops model);
    val names = map (fst o dest_Free);

    val Inj_injs = map2 (@{map_filter 2} (fn Inj => fn Vrs => if body_type (fastype_of Inj) = domain_type (fastype_of Vrs) then
      let
        val ([a, b], _) = lthy |> mk_Frees "a" (replicate 2 (domain_type (fastype_of Inj)));
        val goal = mk_Trueprop_eq (HOLogic.mk_eq (Inj $ a, Inj $ b), HOLogic.mk_eq (a, b));
      in SOME (Goal.prove_sorry lthy (names [a, b]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        rtac ctxt iffI,
        dtac ctxt (mk_arg_cong lthy 1 Vrs),
        K (Local_Defs.unfold0_tac ctxt (flat (maps #Vrs_Injss axioms))),
        etac ctxt @{thm singleton_inject},
        hyp_subst_tac ctxt,
        rtac ctxt refl
      ])) end
      else NONE
    )) (#Injs (#consts model)) (#Vrs (#consts model));

    val Un_bound = MRBNF_Def.get_class_assumption [#var_class model] "Un_bound" lthy;

    val Injss = #Injs (#consts model);

    val (((rhoss, hss), fss), names_lthy) = lthy
      |> mk_Freess "\<rho>" (map (map fastype_of) Injss)
      ||>> mk_Freess "h" (map (map (fn RVrs =>
        let val T = HOLogic.dest_setT (body_type (fastype_of RVrs));
        in T --> T end
      )) (#RVrs (#consts model)))
      ||>> mk_Freess "f" (map2 (map2 (curry (op-->))) (#lives model) (#lives' model));

    val Supp_Injss = @{map 5} (fn lives => fn lives' => fn params => fn Injs => the_default [] o Option.map (fn { Supps, Map } => map (fn Supp => map_filter (fn Inj =>
      if body_type (fastype_of Inj) = domain_type (fastype_of Supp) then
      let
        val a = Free ("a", domain_type (fastype_of Inj))
        val goal = mk_Trueprop_eq (
          Supp $ (Inj $ a), mk_bot (HOLogic.dest_setT (body_type (fastype_of Supp)))
        )
        val Map = Term.subst_atomic_types (lives' ~~ map (K @{typ nat}) lives') Map;
        val SSupp' = Term.subst_atomic_types (lives ~~ map (K @{typ nat}) lives) Supp;
        val thm = Goal.prove_sorry lthy ["a"] [] (mk_Trueprop_eq (
          SSupp' $ (Term.list_comb (Map, map (fn live => Term.abs ("_", live) @{term "0::nat"}) lives) $ (Inj $ a)),
          SSupp' $ (Term.list_comb (Map, map (fn live => Term.abs ("_", live) @{term "1::nat"}) lives) $ (Inj $ a))
        )) (fn {context = ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold_tac ctxt (
            map (fn thm =>  Local_Defs.unfold0 ctxt @{thms comp_def} (thm RS fun_cong)) (#Map_Injs (the params))
          )),
          rtac ctxt refl
        ]);
      in SOME (Goal.prove_sorry lthy ["a"] [] goal (fn {context=ctxt, ...} => EVERY1 [
        Method.insert_tac ctxt [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt a)] thm],
        K (Local_Defs.unfold0_tac ctxt (#Supp_Map (#axioms (the params)))),
        dtac ctxt @{thm image_const_empty[rotated]},
        rtac ctxt @{thm zero_neq_one},
        etac ctxt conjE,
        assume_tac ctxt
      ])) end else NONE
    ) Injs) Supps)) (#lives model) (#lives' model) (#params model) Injss (#params (#consts model))

    val SSupp_premss = @{map 3} (fn Injs => fn rhos => fn hs => 
      map (HOLogic.mk_Trueprop o mk_supp_bound) hs @
      map2 (fn Inj => fn rho => HOLogic.mk_Trueprop (
        mk_ordLess (mk_card_of (mk_SSupp Inj $ rho)) (mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of Inj))))
      )) Injs rhos
    ) Injss rhoss hss;

    val SSupp_thms = @{map 12} (fn params => fn param_consts => fn axioms => fn T => fn SSupp_prems => fn lives => fn lives' => fn fs => fn Injs => fn rhos => fn hs => fn Sb =>
      let
        val SSupp_Map_subsets = Option.map (fn Map => @{map_filter 2} (fn Inj => fn rho =>
          if body_type (fastype_of Inj) <> T then NONE else
          let val goal = HOLogic.mk_Trueprop (
            mk_leq (Term.subst_atomic_types (lives ~~ lives') (
              mk_SSupp Inj
            ) $ HOLogic.mk_comp (Term.list_comb (Map, fs), rho)) (mk_SSupp Inj $ rho)
          ) in SOME (Goal.prove_sorry lthy (names (fs @ [rho])) [] goal (fn {context=ctxt, ...} => EVERY1 [
            rtac ctxt subsetI,
            K (Local_Defs.unfold0_tac ctxt @{thms SSupp_def mem_Collect_eq}),
            etac ctxt @{thm contrapos_nn},
            rtac ctxt @{thm trans[OF comp_apply]},
            etac ctxt @{thm subst[OF sym]},
            rtac ctxt @{thm trans[rotated]},
            resolve_tac ctxt (map (fn thm => thm RS fun_cong) (#Map_Injs (the params))),
            rtac ctxt @{thm comp_apply[symmetric]}
          ])) end
        ) Injs rhos) (Option.map #Map param_consts);

        val SSupp_Map_bounds = Option.map (map (fn thm => @{thm card_of_subset_bound} OF [thm])) SSupp_Map_subsets;

        val SSupp_Sb_subsets = @{map_filter 2} (fn Inj => fn rho => if body_type (fastype_of Inj) <> T then NONE else
          let
            val (rho', _) = names_lthy
              |> apfst hd o mk_Frees "\<rho>'" [fastype_of Inj];
            val goal = HOLogic.mk_Trueprop (mk_leq
              (mk_SSupp Inj $ HOLogic.mk_comp (
                Term.list_comb (Sb, hs @ rhos), rho'
              ))
              (mk_Un (mk_SSupp Inj $ rho, mk_SSupp Inj $ rho'))
            );
          in SOME (Goal.prove_sorry lthy (names (rho' :: hs @ rhos)) SSupp_prems goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt subsetI,
            K (Local_Defs.unfold0_tac ctxt @{thms SSupp_def mem_Collect_eq Un_iff de_Morgan_conj[symmetric]}),
            etac ctxt @{thm contrapos_nn},
            etac ctxt conjE,
            rtac ctxt @{thm trans[OF comp_apply]},
            rotate_tac 1,
            etac ctxt @{thm subst[OF sym]},
            rtac ctxt trans,
            resolve_tac ctxt (map (fn thm => thm RS fun_cong RS @{thm trans[OF comp_apply[symmetric]]}) (#Sb_comp_Injs axioms)),
            REPEAT_DETERM o resolve_tac ctxt prems,
            assume_tac ctxt
          ])) end
        ) Injs rhos;

        val SSupp_Sb_bounds = map_filter (fn Inj => if body_type (fastype_of Inj) <> T then NONE else
          let
            val (rho, _) = names_lthy
              |> apfst hd o mk_Frees "\<rho>'" [fastype_of Inj];
            val card = mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of Inj)));
            val SSupp_prem = HOLogic.mk_Trueprop (mk_ordLess
              (mk_card_of (mk_SSupp Inj $ rho)) card
            );
            val goal = HOLogic.mk_Trueprop (mk_ordLess
              (mk_card_of (mk_SSupp Inj $ HOLogic.mk_comp (
                Term.list_comb (Sb, hs @ rhos), rho
              ))) card
            );
          in SOME (Goal.prove_sorry lthy (names (rho :: hs @ rhos)) (SSupp_prem :: SSupp_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt @{thm card_of_subset_bound},
            resolve_tac ctxt SSupp_Sb_subsets,
            REPEAT_DETERM o resolve_tac ctxt (Un_bound :: prems)
          ])) end
        ) Injs;
      in {
        SSupp_Map_subsets = SSupp_Map_subsets,
        SSupp_Map_bounds = SSupp_Map_bounds,
        SSupp_Sb_subsets = SSupp_Sb_subsets,
        SSupp_Sb_bounds = SSupp_Sb_bounds
      } end
    ) (#params model) (#params (#consts model)) (#tacs model) (#ops model) SSupp_premss (#lives model) (#lives' model) fss Injss rhoss hss (#Sbs (#consts model));

    val facts = @{map 3} (fn Inj_inj => fn SSupp_thms => fn Supp_Injss => {
      Inj_inj = Inj_inj,
      Supp_Injss = Supp_Injss,
      SSupp_Map_subsets = #SSupp_Map_subsets SSupp_thms,
      SSupp_Map_bounds = #SSupp_Map_bounds SSupp_thms,
      SSupp_Sb_subsets = #SSupp_Sb_subsets SSupp_thms,
      SSupp_Sb_bounds = #SSupp_Sb_bounds SSupp_thms
    }: bmv_monad_facts) Inj_injs SSupp_thms Supp_Injss;

    val bmv = BMV {
      ops = #ops model @ maps (#ops o Rep_bmv) (#bmv_ops model),
      var_class = #var_class model,
      leader = #leader model,
      frees = #frees model @ maps (#frees o Rep_bmv) (#bmv_ops model),
      lives = #lives model @ maps (#lives o Rep_bmv) (#bmv_ops model),
      lives' = #lives' model @ maps (#lives' o Rep_bmv) (#bmv_ops model),
      deads = #deads model @ maps (#deads o Rep_bmv) (#bmv_ops model),
      consts = consts,
      params = #params model @ maps (#params o Rep_bmv) (#bmv_ops model),
      axioms = axioms,
      facts = facts @ maps facts_of_bmv_monad (#bmv_ops model),
      bd_infinite_regular_card_order = #bd_infinite_regular_card_order model
    } : bmv_monad;

    val (_, lthy) = note_bmv_monad_thms fact_policy qualify bmv_b_opt bmv lthy;
  in (bmv, lthy) end

fun prove_axioms (model: (Proof.context -> tactic) bmv_monad_model) defs lthy =
  let
    val goals = mk_bmv_monad_axioms (#ops model) (#consts model) (#bmv_ops model) lthy;
    val tacs' = map (map_bmv_monad_axioms (fn tac => fn ctxt => Local_Defs.unfold0_tac ctxt defs THEN tac ctxt)) (#tacs model);
  in (map2 apply_bmv_monad_axioms
    (map (map_bmv_monad_axioms (fn goal => fn tac => Goal.prove_sorry lthy [] [] goal (tac o #context))) goals)
    tacs'
  )
  end;

fun prove_params (model: (Proof.context -> tactic) bmv_monad_model) defs lthy =
  let
    val goals = @{map 5} (fn Sb => fn RVrs => fn Vrs => fn Injs => Option.map (fn param =>
      mk_param_axiom (#Map param) (#Supps param) Sb Injs RVrs Vrs (#bd (#consts model)) (map_filter I (#params (#consts model))) lthy
    )) (#Sbs (#consts model)) (#RVrs (#consts model)) (#Vrs (#consts model)) (#Injs (#consts model)) (#params (#consts model))
    val tacs' = map (Option.map (map_bmv_monad_param (fn tac => fn goal =>
      Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, ...} =>
       Local_Defs.unfold0_tac ctxt defs THEN tac ctxt
     )
    ))) (#params model);
  in map2 (@{map_option 2} (
    fn { axioms=tacs, Map_Sb=f1, Supp_Sb=f2s, Vrs_Map=f3s, Map_Injs=f4s } =>
    fn { axioms, Map_Sb, Supp_Sb, Vrs_Map, Map_Injs } => {
      Map_Sb = f1 Map_Sb,
      Supp_Sb = map2 (curry (op|>)) Supp_Sb f2s,
      Vrs_Map = map2 (curry (op|>)) Vrs_Map f3s,
      Map_Injs = map2 (curry (op|>)) Map_Injs f4s,
      axioms = {
        Map_id = #Map_id tacs (#Map_id axioms),
        Map_comp = #Map_comp tacs (#Map_comp axioms),
        Supp_Map = map2 (curry (op|>)) (#Supp_Map axioms) (#Supp_Map tacs),
        Supp_bd = map2 (curry (op|>)) (#Supp_bd axioms) (#Supp_bd tacs),
        Map_cong = #Map_cong tacs (#Map_cong axioms)
      }
  } : thm bmv_monad_param)) tacs' goals end;

fun mk_thm_model (model: 'a bmv_monad_model) params axioms bd_irco = {
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
  tacs = axioms
} : thm bmv_monad_model;

fun bmv_monad_def const_policy fact_policy qualify bmv_b_opt (model: (Proof.context -> tactic) bmv_monad_model) lthy =
  let
    val frees = map (fn T => TFree (apsnd (
      Sign.minimize_sort (Proof_Context.theory_of lthy) o cons (#var_class model)
    ) (dest_TFree T))) (nth (#frees model) (#leader model));
    val model = morph_bmv_monad_model (MRBNF_Util.subst_typ_morphism (nth (#frees model) (#leader model) ~~ frees)) I model;

    val (consts, unfold_set, lthy) = define_bmv_monad_consts const_policy (fact_policy lthy) qualify
      (#leader model) (#ops model) (#lives' model) (#consts model) lthy;
    val model = update_consts consts model;

    val axioms = prove_axioms model unfold_set lthy;
    val params = prove_params model unfold_set lthy;

    val bd_irco = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (
      mk_infinite_regular_card_order (#bd (#consts model))
    )) (fn {context=ctxt, ...} => Local_Defs.unfold0_tac ctxt unfold_set THEN #bd_infinite_regular_card_order model ctxt);

    val model = mk_thm_model model params axioms bd_irco;
  in apfst (rpair unfold_set) (mk_bmv_monad const_policy fact_policy qualify bmv_b_opt model lthy) end

fun pbmv_monad_of_mrbnf mrbnf lthy =
  let
    val (((((lives, lives'), frees), bounds), deads), names_lthy) = lthy
      |> mk_TFrees (MRBNF_Def.live_of_mrbnf mrbnf)
      ||>> mk_TFrees (MRBNF_Def.live_of_mrbnf mrbnf)
      ||>> mk_TFrees' (map Type.sort_of_atyp (MRBNF_Def.frees_of_mrbnf mrbnf))
      ||>> mk_TFrees' (map Type.sort_of_atyp (MRBNF_Def.bounds_of_mrbnf mrbnf))
      ||>> mk_TFrees' (map Type.sort_of_atyp (MRBNF_Def.deads_of_mrbnf mrbnf));

    val ((fs, gs), _) = names_lthy
      |> mk_Frees "f" (map (fn a => a --> a) frees)
      ||>> mk_Frees "g" (map2 (curry (op-->)) lives lives');
    val T = MRBNF_Def.mk_T_of_mrbnf deads lives bounds frees mrbnf;
    val n = MRBNF_Def.live_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.free_of_mrbnf mrbnf;
    val var_class = case MRBNF_Def.bd_of_mrbnf mrbnf of
      @{term natLeq} => @{class var}
      | _ => error "TODO: other var classes"

    val (lsets, _, fsets) = MRBNF_Def.deinterlace (MRBNF_Def.mk_sets_of_mrbnf
      (replicate n deads) (replicate n lives) (replicate n bounds) (replicate n frees) mrbnf
    ) (MRBNF_Def.var_types_of_mrbnf mrbnf);

    val Sb = if null fs then HOLogic.id_const T else
      fold_rev (Term.absfree o dest_Free) fs (Term.list_comb (
        MRBNF_Def.mk_map_of_mrbnf deads lives lives bounds frees mrbnf,
        MRBNF_Def.interlace (map HOLogic.id_const lives) (map HOLogic.id_const bounds) fs (MRBNF_Def.var_types_of_mrbnf mrbnf)
      ));
    val Map = if null lives then NONE else SOME (
      fold_rev (Term.absfree o dest_Free) gs (Term.list_comb (
        MRBNF_Def.mk_map_of_mrbnf deads lives lives' bounds frees mrbnf,
        MRBNF_Def.interlace gs (map HOLogic.id_const bounds) (map HOLogic.id_const frees) (MRBNF_Def.var_types_of_mrbnf mrbnf)
      ))
    );
   in apfst fst (bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Dont_Note) I NONE {
     ops = [T],
     var_class = var_class,
     leader = 0,
     frees = [frees],
     lives = [lives],
     lives' = [lives'],
     deads = [bounds @ deads],
     bmv_ops = [],
     consts = {
       bd = MRBNF_Def.bd_of_mrbnf mrbnf,
       Injs = [[]],
       Sbs = [Sb],
       Vrs = [[]],
       RVrs = [fsets],
       params = [Option.map (fn Map => {
         Map = Map,
         Supps = lsets
       }) Map]
     },
     params = [Option.map (fn _ => {
       axioms = {
         Map_id = fn ctxt => rtac ctxt (MRBNF_Def.map_id0_of_mrbnf mrbnf) 1,
         Map_comp = fn ctxt => EVERY1 [
           rtac ctxt (trans OF [MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym]),
           REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
           K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
           rtac ctxt refl
         ],
         Supp_Map = map (fn _ => fn ctxt => EVERY1 [
           resolve_tac ctxt (MRBNF_Def.set_map_of_mrbnf mrbnf),
           REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
         ]) lsets,
         Supp_bd = map (fn _ => fn ctxt => resolve_tac ctxt (MRBNF_Def.set_bd_of_mrbnf mrbnf) 1) lsets,
         Map_cong = fn ctxt => EVERY1 [
           rtac ctxt (MRBNF_Def.map_cong0_of_mrbnf mrbnf),
           REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
           REPEAT_DETERM o (rtac ctxt refl ORELSE' Goal.assume_rule_tac ctxt)
         ]
       },
       Map_Sb = fn ctxt => EVERY1 [
         K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
         rtac ctxt refl ORELSE' EVERY' [
           rtac ctxt (trans OF [MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym]),
           REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
           rtac ctxt sym,
           rtac ctxt (trans OF [MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym]),
           REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
           K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
           rtac ctxt refl
         ]
       ],
       Supp_Sb = map (fn _ => fn ctxt => EVERY1 [
         K (Local_Defs.unfold0_tac ctxt @{thms id_apply}),
         rtac ctxt refl ORELSE' EVERY' [
           rtac ctxt trans,
           resolve_tac ctxt (MRBNF_Def.set_map_of_mrbnf mrbnf),
           REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
           rtac ctxt @{thm image_id}
         ]
       ]) lsets,
       Vrs_Map = map (fn _ => fn ctxt => EVERY1 [
         rtac ctxt trans,
         resolve_tac ctxt (MRBNF_Def.set_map_of_mrbnf mrbnf),
         REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound},
         rtac ctxt @{thm image_id}
       ]) fsets,
       Map_Injs = []
     }) Map],
     bd_infinite_regular_card_order = fn ctxt => rtac ctxt (MRBNF_Def.bd_infinite_regular_card_order_of_mrbnf mrbnf) 1,
     tacs = [{
       Sb_Inj = fn ctxt => resolve_tac ctxt [refl, MRBNF_Def.map_id0_of_mrbnf mrbnf] 1,
       Sb_comp_Injs = [],
       Sb_comp = fn ctxt => EVERY1 [
         TRY o EVERY' [
           rtac ctxt (trans OF [MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym]),
           REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
         ],
         K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
         rtac ctxt refl
       ],
       Vrs_bds = map (fn _ => fn ctxt => resolve_tac ctxt (MRBNF_Def.set_bd_of_mrbnf mrbnf) 1) fsets,
       Vrs_Injss = [],
       Vrs_Sbs = map (fn _ => fn ctxt => EVERY1 [
         resolve_tac ctxt (MRBNF_Def.set_map_of_mrbnf mrbnf),
         REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
       ]) fsets,
       Sb_cong = fn ctxt => rtac ctxt refl 1 ORELSE EVERY1 [
         rtac ctxt (MRBNF_Def.map_cong0_of_mrbnf mrbnf),
         REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
         REPEAT_DETERM o (rtac ctxt refl ORELSE' Goal.assume_rule_tac ctxt)
       ]
     }]
   } lthy) end;

fun register_mrbnf_as_pbmv_monad name lthy =
  let
    val mrbnf = the (MRBNF_Def.mrbnf_of lthy name);
    val (bmv, lthy) = pbmv_monad_of_mrbnf mrbnf lthy;
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
  in BMV {
    ops = [f (ops_of_bmv_monad bmv)],
    var_class = var_class_of_bmv_monad bmv,
    leader = 0,
    frees = [f (frees_of_bmv_monad bmv)],
    lives = [f (lives_of_bmv_monad bmv)],
    lives' = [f (lives'_of_bmv_monad bmv)],
    deads = [f (deads_of_bmv_monad bmv)],
    consts = {
      bd = bd_of_bmv_monad bmv,
      params = [@{map_option 2} (fn Map => fn Supps => {
        Map = Map, Supps = Supps
      }) (f (Maps_of_bmv_monad bmv)) (f (Supps_of_bmv_monad bmv))],
      Injs = [f (Injs_of_bmv_monad bmv)],
      Sbs = [Sb],
      RVrs = [f (RVrs_of_bmv_monad bmv)],
      Vrs = [f (Vrs_of_bmv_monad bmv)]
    },
    params = [f (params_of_bmv_monad bmv)],
    bd_infinite_regular_card_order = bd_infinite_regular_card_order_of_bmv_monad bmv,
    axioms = [f (axioms_of_bmv_monad bmv)],
    facts = [f (facts_of_bmv_monad bmv)]
  } end;

fun compose_bmv_monad qualify (outer : bmv_monad) (inners : (bmv_monad, typ) either list)
  (oAs: { frees: typ list, deads: typ list }) (Ass : ({ frees: typ list, lives: typ list, deads: typ list }) option list) lthy =
  let
    val _ = if length (nth (lives_of_bmv_monad outer) (leader_of_bmv_monad outer)) <> length inners then
      error "Outer needs exactly as many lives as there are inners" else ()

    fun leader f bmv = nth (f bmv) (leader_of_bmv_monad bmv)

    val eq_name = (op=) o apply2 (fst o dest_TFree)
    val deads = distinct eq_name (
      #deads oAs @ flat (map2 (fn SOME { deads, ...} => K deads |
        NONE => fn Inr T => map TFree (rev (Term.add_tfreesT T []))
      ) Ass inners)
    );
    (* TODO: other bounds *)
    val frees = map (resort_tfree_or_tvar @{sort var}) (distinct eq_name (#frees oAs @ flat (map_filter (Option.map #frees) Ass)))
    val killed_frees = inter eq_name deads frees;
    val deads = map (fn d => the_default d (List.find (curry eq_name d) killed_frees)) deads;
    val frees = subtract eq_name deads frees;

    val lives = subtract eq_name (deads @ frees) (
      distinct eq_name (flat (map_filter (Option.map #lives) Ass))
    );
    val vars = deads @ frees @ lives;

    val (lives', names_lthy) = lthy
      |> fold Variable.declare_typ vars
      |> mk_TFrees (length lives);

    fun find_vars xs = map (fn x => the (
      List.find (curry eq_name x) vars
    )) xs;
    val inners = map2 (fn As => map_sum (fn bmv =>
      let
        val new_frees = find_vars (#frees (the As));
        val new_deads = find_vars (#deads (the As));
        val new_lives = find_vars (#lives (the As));
        val new_lives' = map (fn a => case find_index (curry (op=) a) lives of
          ~1 => a | i => nth lives' i
        ) new_lives;

        val phi = MRBNF_Util.subst_typ_morphism (
          (leader frees_of_bmv_monad bmv ~~ new_frees)
          @ (leader deads_of_bmv_monad bmv ~~ new_deads)
          @ (leader lives_of_bmv_monad bmv ~~ new_lives)
          @ (leader lives'_of_bmv_monad bmv ~~ new_lives')
        );
      in morph_bmv_monad phi bmv end
    ) (fn T =>
      let
        val old_vars = map TFree (Term.add_tfreesT T []);
        val subst = map (fn a => (a, the (List.find (curry eq_name a) vars))) old_vars;
      in Term.typ_subst_atomic subst T end
    )) Ass inners;
    val outer =
      let
        val new_frees = find_vars (#frees oAs);
        val new_deads = find_vars (#deads oAs);
        val new_lives = map (either (leader ops_of_bmv_monad) I) inners;
        val new_lives' = map (Term.typ_subst_atomic (lives ~~ lives')) new_lives;

        val phi = MRBNF_Util.subst_typ_morphism (
          (leader frees_of_bmv_monad outer ~~ new_frees)
          @ (leader deads_of_bmv_monad outer ~~ new_deads)
          @ (leader lives_of_bmv_monad outer ~~ new_lives)
          @ (leader lives'_of_bmv_monad outer ~~ new_lives')
        );
      in morph_bmv_monad phi outer end;

    val inners' = map_filter (fn Inl x => SOME x | _ => NONE) inners;

    val (x, _) = names_lthy
      |> apfst hd o mk_Frees "x" [leader ops_of_bmv_monad outer];

    val new_Injs = filter (member (op=) frees o domain_type o fastype_of) (
      maps (leader Injs_of_bmv_monad) (outer :: inners')
    );
    
    fun option x f y = the_default x (Option.map f y)
    val new_RVrs = map_filter (fn a =>
      let
        fun get_RVrs bmv = List.find (curry (op=) a o HOLogic.dest_setT o body_type o fastype_of) (
          (if null (leader lives_of_bmv_monad bmv) then [] else
            @{map_filter 3} (fn l => fn l' => fn set =>
              if l = l' then SOME set else NONE
            ) (leader lives_of_bmv_monad bmv) (leader lives'_of_bmv_monad bmv) (the (leader Supps_of_bmv_monad bmv))
          ) @ leader RVrs_of_bmv_monad bmv
        );
        val outer_RVrs = option [] (fn set => [set $ x]) (get_RVrs outer);
        val inner_RVrs = @{map_filter 2} (fn Inr _ => K NONE | Inl inner => fn set => Option.map (fn RVrs =>
          mk_UNION (set $ x) RVrs
        ) (get_RVrs inner)) inners (the (leader Supps_of_bmv_monad outer))
      in Option.map (Term.absfree (dest_Free x)) (
        try (foldl1 mk_Un) (outer_RVrs @ inner_RVrs)
      ) end
    ) frees;

    val new_Vrs = map (fn Inj =>
      let
        fun get_Vrs bmv = case find_index ((op=) o apply2 fastype_of o pair Inj) (leader Injs_of_bmv_monad bmv) of
          ~1 => NONE | n => SOME (nth (leader Vrs_of_bmv_monad bmv) n);

        val outer_Vrs = option [] (fn Vr => [Vr $ x]) (get_Vrs outer);
        val inner_Vrs = @{map_filter 2} (fn Inr _ => K NONE | Inl inner => fn set => Option.map (fn Vr =>
          mk_UNION (set $ x) Vr
        ) (get_Vrs inner)) inners (the (leader Supps_of_bmv_monad outer));
      in Term.absfree (dest_Free x) (foldl1 mk_Un (outer_Vrs @ inner_Vrs)) end
    ) new_Injs;

    val (((hs, rhos), fs), _) = names_lthy
      |> mk_Frees "h" (map (fn Vr => let val T = HOLogic.dest_setT (body_type (fastype_of Vr)) in T --> T end) new_RVrs)
      ||>> mk_Frees "\<rho>" (map fastype_of new_Injs)
      ||>> mk_Frees "f" (map2 (curry (op-->)) lives lives');

    val new_Sb =
      let
        val osubst = lives' ~~ lives;
        val map_t = Term.list_comb (Term.subst_atomic_types osubst (
          the (leader Maps_of_bmv_monad outer)
        ), map (fn Inr T => HOLogic.id_const T | Inl inner =>
          let
            val lives = leader lives_of_bmv_monad inner;
            val lives' = leader lives'_of_bmv_monad inner;
            val map_t_opt = if null lives orelse forall (op<>) (lives ~~ lives') then NONE else SOME (
              Term.list_comb (
                Term.subst_atomic_types (lives' ~~ lives) (the (leader Maps_of_bmv_monad inner)),
                map (fn a =>
                  case List.find (curry (op=) a o domain_type o fastype_of) hs of
                    NONE => HOLogic.id_const a | SOME h => h
                ) lives
              )
            );
            val Sb_t = Term.list_comb (leader Sbs_of_bmv_monad inner, map_filter (fn RVr =>
              List.find (curry (op=) (HOLogic.dest_setT (body_type (fastype_of RVr))) o domain_type o fastype_of) hs
            ) (leader RVrs_of_bmv_monad inner) @ map (fn Inj =>
              case List.find (curry (op=) (fastype_of Inj) o fastype_of) rhos of
                NONE => Inj | SOME rho => rho
            ) (leader Injs_of_bmv_monad inner));
            val mk_Map_comp = case map_t_opt of
              NONE => I | SOME t => fn t' => HOLogic.mk_comp (t, t')
          in mk_Map_comp Sb_t end
        ) inners);
        val add_Sb = if null (leader RVrs_of_bmv_monad outer @ leader Vrs_of_bmv_monad outer) then I else fn t => HOLogic.mk_comp (t,
          Term.list_comb (leader Sbs_of_bmv_monad outer, map (fn RVrs =>
            let val T = HOLogic.dest_setT (body_type (fastype_of RVrs));
            in the_default (HOLogic.id_const T) (List.find (curry (op=) T o domain_type o fastype_of) hs) end
          ) (leader RVrs_of_bmv_monad outer) @ map (fn Inj => the_default Inj (
            List.find (curry (op=) (fastype_of Inj) o fastype_of) rhos
          )) (leader Injs_of_bmv_monad outer)
        ));
      in fold_rev (Term.absfree o dest_Free) (hs @ rhos) (add_Sb map_t) end;

    val param = if null lives then NONE else
      let
        val Map = fold_rev (Term.absfree o dest_Free) fs (
          Term.list_comb (the (leader Maps_of_bmv_monad outer),
            map (fn Inr T => HOLogic.id_const T | Inl inner => if null (leader lives_of_bmv_monad inner) then
              HOLogic.id_const (leader ops_of_bmv_monad inner) else Term.list_comb (the (leader Maps_of_bmv_monad inner), 
                map (fn l => the_default (HOLogic.id_const l)
                  (List.find (curry (op=) l o domain_type o fastype_of) fs)
                ) (leader lives_of_bmv_monad inner)
              )
            ) inners
          )
        );
        val Supps = map (fn live => Term.absfree (dest_Free x) (foldl1 mk_Un (@{map_filter 2} (
          fn Inr _ => K NONE | Inl inner => fn set => if null (leader lives_of_bmv_monad inner) then NONE
            else Option.map (mk_UNION (set $ x)) (
              List.find (curry (op=) live o HOLogic.dest_setT o body_type o fastype_of) (the (leader Supps_of_bmv_monad inner))
            )
          ) inners (the (leader Supps_of_bmv_monad outer))))) lives;
      in SOME { Map = Map, Supps = Supps } end;

    val consts = {
      bd = bd_of_bmv_monad outer, (* TODO: compose bounds *)
      Injs = [new_Injs],
      Sbs = [new_Sb],
      Vrs = [new_Vrs],
      RVrs = [new_RVrs],
      params = [param]
    }: bmv_monad_consts;

    val new_minions = map (fn bmv => (hd (ops_of_bmv_monad bmv), bmv)) (
      filter_out (curry (op=) (leader ops_of_bmv_monad outer) o hd o ops_of_bmv_monad) (
        distinct ((op=) o apply2 (hd o ops_of_bmv_monad)) (outer :: inners')
      )
    );
    val new_minions = map_filter (AList.lookup (op=) new_minions o body_type o fastype_of) new_Injs;
    val axiomss = map (leader axioms_of_bmv_monad) inners';

    val model = {
      ops = [leader ops_of_bmv_monad outer],
      bmv_ops = new_minions,
      bd_infinite_regular_card_order = fn ctxt => rtac ctxt (bd_infinite_regular_card_order_of_bmv_monad outer) 1,
      var_class = var_class_of_bmv_monad outer,
      frees = [frees],
      lives = [lives],
      lives' = [lives'],
      deads = [deads],
      consts = consts,
      params = [Option.map (fn { Supps, ...} => {
        axioms = {
          Map_id = fn ctxt => EVERY1 [
            K (print_tac ctxt "Map_id")
          ],
          Map_comp = fn ctxt => EVERY1 [
            K (print_tac ctxt "Map_comp")
          ],
          Supp_Map = map (fn _ => fn ctxt => EVERY1 [
            K (print_tac ctxt "Supp_map")
          ]) Supps,
          Supp_bd = map (fn _ => fn ctxt => EVERY1 [
            K (print_tac ctxt "Supp_bd")
          ]) Supps,
          Map_cong = fn ctxt => EVERY1 [
            K (print_tac ctxt "Map_cong")
          ]
        },
        Map_Sb = fn ctxt => EVERY1 [
          K (print_tac ctxt "Map_id")
        ],
        Supp_Sb = map (fn _ => fn ctxt => EVERY1 [
          K (print_tac ctxt "Map_id")
        ]) Supps,
        Vrs_Map = map (fn _ => fn ctxt => EVERY1 [
          K (print_tac ctxt "Map_id")
        ]) new_Vrs,
        Map_Injs = map (fn _ => fn ctxt => EVERY1 [
          K (print_tac ctxt "Map_Injs")
        ]) new_Injs
      }) param],
      leader = 0,
      tacs = @{map 6} (fn axioms => fn param => fn Map => fn Injs => fn RVrs => fn Vrs => {
        Sb_Inj = fn ctxt => EVERY1 [
          K (Local_Defs.unfold_tac ctxt (@{thms id_o o_id}
            @ map #Sb_Inj (axioms :: axiomss)
            @ [#Map_id (#axioms param)]
            @ map_filter (Option.map (#Map_id o #axioms) o leader params_of_bmv_monad) inners'
          )),
          rtac ctxt refl
        ],
        Sb_comp_Injs = map (fn thm => fn ctxt => EVERY1 [
          K (print_tac ctxt "Sb_comp_Inj")
        ]) (#Sb_comp_Injs axioms),
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
            EqSubst.eqsubst_tac ctxt [0] (@{thm id_o} :: maps (map #Sb_comp o axioms_of_bmv_monad) inners'),
            REPEAT_DETERM o assume_tac ctxt,
            rtac ctxt refl
          ]
        ],
        Vrs_bds = map (K (fn ctxt => EVERY1 [
          REPEAT_DETERM o resolve_tac ctxt (
            #Vrs_bds axioms
            @ maps (maps #Vrs_bds o axioms_of_bmv_monad) inners'
            @ #Supp_bd (#axioms param)
            @ map (fn thm =>
              thm OF [bd_infinite_regular_card_order_of_bmv_monad outer]
            ) @{thms infinite_regular_card_order_Un infinite_regular_card_order_UN}
          )
        ])) (RVrs @ Vrs),
        Vrs_Injss = map (map (fn thm => fn ctxt =>
          print_tac ctxt "Vrs_Injs"
        )) (#Vrs_Injss axioms),
        Vrs_Sbs = map (K (fn ctxt => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (
            @{thms image_Un image_UN comp_def image_comp Union_UN_swap}
            @ #Vrs_Map param
            @ #Supp_Sb param
            @ #Supp_Map (#axioms param)
          )),
          REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
          TRY o (resolve_tac ctxt (#Vrs_Sbs axioms) THEN_ALL_NEW assume_tac ctxt),
          REPEAT_DETERM o EVERY' [
            rtac ctxt @{thm UN_cong},
            resolve_tac ctxt (maps (maps #Vrs_Sbs o axioms_of_bmv_monad) inners'),
            REPEAT_DETERM o assume_tac ctxt
          ]
        ])) (RVrs @ Vrs),
        Sb_cong = fn ctxt => EVERY1 [
          rtac ctxt @{thm comp_apply_eq},
          Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
            rtac ctxt @{thm trans[rotated]},
            rtac ctxt (
              let val n = length (nth (lives_of_bmv_monad outer) (leader_of_bmv_monad outer));
              in mk_arg_cong lthy (n + 1) Map OF (replicate n refl) end
            ),
            K (prefer_tac 2),
            rtac ctxt (#Map_cong (#axioms param)),
            EVERY' (map (fn Inr _ => rtac ctxt refl | Inl inner => EVERY' [
              EqSubst.eqsubst_asm_tac ctxt [0] (#Supp_Sb param),
              REPEAT_DETERM o resolve_tac ctxt prems,
              resolve_tac ctxt (map #Sb_cong (axioms_of_bmv_monad inner)),
              REPEAT_DETERM o resolve_tac ctxt (take (2 * length Injs) prems),
              REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
                TRY o (dtac ctxt @{thm UN_I} THEN' assume_tac ctxt),
                resolve_tac ctxt (drop (2 * length Injs) prems),
                REPEAT_DETERM o FIRST' [
                  assume_tac ctxt,
                  etac ctxt UnI2,
                  rtac ctxt UnI1
                ]
              ])
            ]) inners),
            TRY o EVERY' [
              rtac ctxt (#Sb_cong axioms),
              REPEAT_DETERM o resolve_tac ctxt (take (2 * length Injs) prems),
              REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
                TRY o (dtac ctxt @{thm UN_I} THEN' assume_tac ctxt),
                resolve_tac ctxt (drop (2 * length Injs) prems),
                REPEAT_DETERM o FIRST' [
                  assume_tac ctxt,
                  etac ctxt UnI2,
                  rtac ctxt UnI1
                ]
              ])
            ]
          ]) ctxt
        ]
      } : (Proof.context -> tactic) bmv_monad_axioms)
      [leader axioms_of_bmv_monad outer]
      [the (leader params_of_bmv_monad outer)]
      [the (leader Maps_of_bmv_monad outer)]
      [new_Injs] [new_RVrs] [new_Vrs]
    } : (Proof.context -> tactic) bmv_monad_model;

    val name = qualify (Binding.conglomerate (map_filter (
      try (Binding.name o short_type_name o fst o dest_Type) o leader ops_of_bmv_monad
    ) (outer :: inners')));
    val (res, lthy) = bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Dont_Note) qualify (SOME name) model lthy
  in (res, lthy) end;

fun pbmv_monad_cmd ((((((b_ops, Sbs), RVrs), Injs), Vrs), param_opt), bd) lthy =
  let
    val b = fst (hd b_ops);
    val (opss, bmv_ops) = split_list (map_index (fn (i, (b, s)) =>
      let
        val T = Syntax.read_typ lthy s
        val name = if Binding.is_empty b then fst (dest_Type T) else Local_Theory.full_name lthy b
      in the_default ([T], NONE) (Option.map (fn bmv =>
        let
          val T' = nth (ops_of_bmv_monad bmv) (leader_of_bmv_monad bmv);
          val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
            (Logic.varifyT_global T, T')
            Vartab.empty;
          val T = Term.typ_subst_atomic (map (fn (x, (s, y)) =>
            let val T = Logic.unvarifyT_global (TVar (x, s));
            in (T, resort_tfree_or_tvar (Type.sort_of_atyp y) T) end
          ) (Vartab.dest tyenv)) T;
          val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
            (T', T) Vartab.empty;
          val phi = MRBNF_Util.subst_typ_morphism (map (fn (x, (s, y)) => (TVar (x, s), y)) (Vartab.dest tyenv));
          val bmv = morph_bmv_monad phi bmv;
        in (ops_of_bmv_monad bmv, SOME bmv) end
      ) (if i = 0 then NONE else pbmv_monad_of lthy name)) end
    ) b_ops);

    val ops = @{map_filter 2} (fn NONE => SOME o hd | SOME _ => K NONE) bmv_ops opss;
    val bmv_ops = map_filter I bmv_ops;

    val bd = Syntax.read_term lthy bd;
    val (ops, Sbs) = split_list (map2 (fn Sb => fn T => 
      let
        val body_T = Logic.varifyT_global (body_type (fastype_of Sb));
        val (tyenv, _) = Sign.typ_unify (Proof_Context.theory_of lthy)
          (Logic.varifyT_global T, Logic.incr_tvar (maxidx_of_typ body_T + 1) body_T)
          (Vartab.empty, maxidx_of_typ body_T + 1);
        val T = Term.typ_subst_atomic (map_filter (fn (x, (s, y)) =>
          if snd x = 0 then
            let val T = Logic.unvarifyT_global (TVar (x, s));
            in SOME (T, resort_tfree_or_tvar (Type.sort_of_atyp y) T) end
          else NONE
        ) (Vartab.dest tyenv)) T;
        val tyenv = fold (Sign.typ_match (Proof_Context.theory_of lthy)) [
          (Logic.varifyT_global (body_type (fastype_of Sb)), T),
          (Logic.varifyT_global (snd (split_last (binder_types (fastype_of Sb)))), T)
        ] Vartab.empty;
      in (T, Envir.subst_term (tyenv, Vartab.empty) (Logic.varify_types_global Sb)) end
    ) (map (Syntax.read_term lthy) Sbs) ops);

    val f_Tss = map (fst o split_last o binder_types o fastype_of) Sbs;

    val frees' = map (distinct (op=) o map (fst o dest_funT)) f_Tss;
    (* TODO: other var classes *)
    val frees = map (map (resort_tfree_or_tvar @{sort var})) frees';

    val bmv_ops = map (morph_bmv_monad (MRBNF_Util.subst_typ_morphism (hd frees' ~~ hd frees))) bmv_ops;
    val ops = map (Term.typ_subst_atomic (hd frees' ~~ hd frees)) ops;
    val Sbs = map (Term.subst_atomic_types (hd frees' ~~ hd frees)) Sbs;
    val f_Tss = map (fst o split_last o binder_types o fastype_of) Sbs;

    val b = if Binding.is_empty b then fst (dest_Type (hd ops)) else Local_Theory.full_name lthy b

    val vars = distinct (op=) (rev (map TFree (fold Term.add_tfreesT ops [])));

    val names_lthy = lthy
      |> fold Variable.declare_typ vars

    val (lives, lives', param_consts) = case param_opt of
      NONE => (replicate (length ops) [], replicate (length ops) [], replicate (length ops) NONE)
      | SOME (Maps, Suppss) =>
        let
          val Maps = map (fn "_" => NONE | s => SOME (Syntax.read_term lthy s)) Maps;
          val Suppss = map (fn [] => NONE | xs => SOME (map (Syntax.read_term lthy) xs)) Suppss;
          val Maps = Maps @ replicate (length ops - length Maps) NONE;

          val lives = map2 (fn T => the_default [] o Option.map (fn Map =>
            let
              val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
                (Logic.varifyT_global (snd (split_last (binder_types (fastype_of Map)))), T) Vartab.empty;
              val Map = Envir.subst_term (tyenv, Vartab.empty) (Logic.varify_types_global Map);
            in map (fst o dest_funT) (fst (split_last (binder_types (fastype_of Map)))) end
          )) ops Maps;
          val (lives', _) = names_lthy
            |> fold_map mk_TFrees (map length lives);

          val Maps = @{map 4} (fn T => fn lives => fn lives' => Option.map (fn Map =>
            let
              val tyenv = fold (Sign.typ_match (Proof_Context.theory_of lthy)) [
                (Logic.varifyT_global (snd (split_last (binder_types (fastype_of Map)))), T),
                (Logic.varifyT_global (body_type (fastype_of Map)), Term.typ_subst_atomic (lives ~~ lives') T)
              ] Vartab.empty;
            in Envir.subst_term (tyenv, Vartab.empty) (Logic.varify_types_global Map) end
          )) ops lives lives' Maps;

          val Suppss = map2 (fn T => Option.map (map (fn Supp =>
            let val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
              (Logic.varifyT_global (domain_type (fastype_of Supp)), T) Vartab.empty;
            in Envir.subst_term (tyenv, Vartab.empty) (Logic.varify_types_global Supp) end
          ))) ops (Suppss @ replicate (length ops - length Suppss) NONE);

        in (lives, lives',
          map2 (@{map_option 2} (fn Map => fn Supps => { Map = Map, Supps = Supps })) Maps Suppss
        ) end;

    val deadss = @{map 3} (fn frees => fn lives => fn T =>
      subtract (op=) (frees @ lives) (rev (map TFree (Term.add_tfreesT T [])))
    ) frees lives ops;

    val subst = map (fn a => (resort_tfree_or_tvar @{sort type} a, a)) (hd deadss);
    val ops = map (Term.typ_subst_atomic subst) ops;
    val bmv_ops = map (morph_bmv_monad (MRBNF_Util.subst_typ_morphism subst)) bmv_ops;

    val Injs = map (map (fn s =>
      let
        val t = Syntax.read_term lthy s;
        val tyenvs = map_filter (fn T => try (
          Sign.typ_match (Proof_Context.theory_of lthy)
          (Logic.varifyT_global (body_type (fastype_of t)), T))
          Vartab.empty
        ) (ops @ maps ops_of_bmv_monad bmv_ops);
        val t = case tyenvs of
          [] => raise TYPE ("An injection needs to return one of the operators of the BMV Monad, but "
            ^ Syntax.string_of_term lthy t ^ " has type " ^ Syntax.string_of_typ lthy (fastype_of t) ^ ", operators are:", ops, [])
          | tyenv::_ => Envir.subst_term (tyenv, Vartab.empty) (Logic.varify_types_global t);
        in t end
    )) (the_default (replicate (length ops) []) Injs);

    val _ = @{map 4} (fn Sb => fn T => fn Injs => fn f_Ts => map (fn f_T => case List.find (curry (op=) f_T o fastype_of) Injs of
      NONE => raise TYPE ("\n\nExpected injection of type \n" ^ Syntax.string_of_typ lthy f_T ^ "\nfor operator \n" ^ Syntax.string_of_typ lthy T
          ^ "\n\nSubstitution has type " ^ Syntax.string_of_typ lthy (fastype_of Sb) ^ "\nbut got injections:", map fastype_of Injs, [])
      | _ => ()
    ) (filter_out ((op=) o dest_funT) f_Ts)) Sbs ops Injs f_Tss;

    val Vrs = map (map (Syntax.read_term lthy)) (the_default (replicate (length ops) []) Vrs);
    val Vrs = map2 (fn T => map (fn Vr =>
      let val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
        (Logic.varifyT_global (domain_type (fastype_of Vr)), T) Vartab.empty;
      in Envir.subst_term (tyenv, Vartab.empty) (Logic.varify_types_global Vr) end
    )) ops Vrs;

    val RVrs = map (map (Syntax.read_term lthy)) (the_default (replicate (length ops) []) RVrs);
    val RVrs = map2 (fn T => map (fn RVr =>
      let val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
        (Logic.varifyT_global (domain_type (fastype_of RVr)), T) Vartab.empty;
      in Envir.subst_term (tyenv, Vartab.empty) (Logic.varify_types_global RVr) end
    )) (take (length RVrs) ops) RVrs;
    val RVrs = RVrs @ replicate (length Injs - length RVrs) [];

    val Injs = map (map (Term.subst_atomic_types subst)) Injs;
    val Vrs = map (map (Term.subst_atomic_types subst)) Vrs;
    val RVrs = map (map (Term.subst_atomic_types subst)) RVrs;
    val Sbs = map (Term.subst_atomic_types subst) Sbs;

    val param_consts = map (Option.map (fn { Map, Supps } => {
      Map = Term.subst_atomic_types subst Map,
      Supps = map (Term.subst_atomic_types subst) Supps
     })) param_consts;

    val consts = {
      bd = bd,
      Injs = Injs,
      Sbs = Sbs,
      Vrs = Vrs,
      RVrs = RVrs,
      params = param_consts
    }: bmv_monad_consts;
    val (consts, bmv_defs, lthy) = define_bmv_monad_consts BNF_Def.Smart_Inline BNF_Def.Dont_Note I 0
      ops lives' consts lthy;

    val param_goals = @{map 5} (fn Sb => fn Injs => fn RVrs => fn Vrs => Option.map (fn { Map, Supps } =>
      mk_param_axiom Map Supps Sb Injs RVrs Vrs bd (map_filter I (#params consts @ maps (#params o consts_of_bmv_monad) bmv_ops)) lthy
    )) Sbs Injs RVrs Vrs (#params consts);

    val goals = mk_bmv_monad_axioms ops consts bmv_ops lthy;

    fun after_qed thmss lthy =
      let
        val thms = map hd thmss;
        val bd_irco = hd thms;

        val ((axioms, params), _) = apfst split_list (@{fold_map 3} (fn goal => fn param => fn param_consts => fn thms =>
          let
            val (((((((Sb_Inj, Sb_comp_Injs), Sb_comp), Vrs_bds), Vrs_Injss), Vrs_Sbs), Sb_cong), thms) = thms
              |> apfst hd o chop 1
              ||>> chop (length (#Sb_comp_Injs goal))
              ||>> apfst hd o chop 1
              ||>> chop (length (#Vrs_bds goal))
              ||>> fold_map (chop o length) (#Vrs_Injss goal)
              ||>> chop (length (#Vrs_Sbs goal))
              ||>> apfst hd o chop 1;
            val (param, thms) = case param of NONE => (NONE, thms) | SOME goals =>
              let val (((((((((Map_id, Map_comp), Supp_maps), Supp_bds), Map_cong), Map_Sb), Supp_Sb), Vrs_Map), Map_Injs), thms) = thms
                |> apfst hd o chop 1
                ||>> apfst hd o chop 1
                ||>> chop (length (#Supps (the param_consts)))
                ||>> chop (length (#Supps (the param_consts)))
                ||>> apfst hd o chop 1
                ||>> apfst hd o chop 1
                ||>> chop (length (#Supps (the param_consts)))
                ||>> chop (length (#Vrs_Map goals))
                ||>> chop (length (#Map_Injs goals))
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
                Vrs_Map = Vrs_Map,
                Map_Injs = Map_Injs
              } : thm bmv_monad_param), thms) end;
          in ((({
            Sb_Inj = Sb_Inj,
            Sb_comp_Injs = Sb_comp_Injs,
            Sb_comp = Sb_comp,
            Vrs_bds = Vrs_bds,
            Vrs_Injss = Vrs_Injss,
            Vrs_Sbs = Vrs_Sbs,
            Sb_cong = Sb_cong
          }: thm bmv_monad_axioms), param), thms) end
        ) goals param_goals param_consts (tl thms));

        val model = {
          ops = ops,
          var_class = @{class var}, (* TODO: change *)
          leader = 0,
          frees = frees,
          lives = lives,
          lives' = lives',
          deads = deadss,
          bmv_ops = bmv_ops,
          consts = consts,
          params = params,
          bd_infinite_regular_card_order = bd_irco,
          tacs = axioms
        } : thm bmv_monad_model;

        val (bmv, lthy) = mk_bmv_monad BNF_Def.Smart_Inline (K BNF_Def.Note_Some) I (SOME (Binding.name b)) model lthy;

        val lthy = register_pbmv_monad b bmv lthy;
      in lthy end;
  in Proof.theorem NONE after_qed (map (single o rpair []) (
    [HOLogic.mk_Trueprop (mk_infinite_regular_card_order bd)]
    @ flat (map2 (fn goal => fn param => #Sb_Inj goal :: #Sb_comp_Injs goal @ [#Sb_comp goal]
      @ #Vrs_bds goal @ flat (#Vrs_Injss goal) @ #Vrs_Sbs goal
      @ [#Sb_cong goal] @ the_default [] (Option.map (fn param =>
        [#Map_id (#axioms param), #Map_comp (#axioms param)] @ #Supp_Map (#axioms param)
        @ #Supp_bd (#axioms param) @ [#Map_cong (#axioms param), #Map_Sb param]
        @ #Supp_Sb param @ #Vrs_Map param @ #Map_Injs param
      ) param)
    ) goals param_goals)
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
    fun pretty_mrbnf (key, bmv as BMV {ops, frees, lives, deads, consts, leader, ...}) =
      Pretty.big_list
        (Pretty.string_of (Pretty.block ([Pretty.str key, Pretty.str ":", Pretty.brk 1] @
          and_list (map (Pretty.quote o Syntax.pretty_typ ctxt) ops))))
        ([Pretty.block [Pretty.str "frees:", Pretty.brk 1, Pretty.str (string_of_int (length (nth frees leader))),
            Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) (nth frees leader))]] @
          (if length lives > 0 then
            [Pretty.block [Pretty.str "live:", Pretty.brk 1, Pretty.str (string_of_int (length (nth lives leader))),
              Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) (nth lives leader))]]
          else []) @
          (if length deads > 0 then
            [Pretty.block [Pretty.str "dead:", Pretty.brk 1, Pretty.str (string_of_int (length (nth deads leader))),
              Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) (nth deads leader))]]
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
  ((Parse.and_list1 (parse_opt_binding_colon -- Parse.typ) --
    ((Parse.reserved "Sbs" -- @{keyword ":"}) |-- Parse.and_list1 Parse.term) --
    (Scan.option ((Parse.reserved "RVrs" -- @{keyword ":"}) |-- Parse.and_list1 (Scan.repeat1 (Scan.unless (Parse.reserved "Injs" || Parse.reserved "bd" || Parse.reserved "Maps") Parse.term)))) --
    (Scan.option ((Parse.reserved "Injs" -- @{keyword ":"}) |-- Parse.and_list1 (Scan.repeat1 (Scan.unless (Parse.reserved "Vrs") Parse.term)))) --
    (Scan.option ((Parse.reserved "Vrs" -- @{keyword ":"}) |-- Parse.and_list1 (Scan.repeat1 (Scan.unless (Parse.reserved "SSupps" || Parse.reserved "Maps" || Parse.reserved "bd") Parse.term)))) --
    Scan.option (
      ((Parse.reserved "Maps" -- @{keyword ":"}) |-- Parse.and_list1 (Parse.underscore || Parse.term)) --
      ((Parse.reserved "Supps" -- @{keyword ":"}) |-- Parse.and_list1 (
        (Parse.underscore >> K []) ||
        Scan.repeat1 (Scan.unless (Parse.reserved "bd") Parse.term)
      ))
    ) --
    ((Parse.reserved "bd" -- @{keyword ":"}) |-- Parse.term))
  >> pbmv_monad_cmd)

end