signature BMV_MONAD_DEF = sig
  type bmv_monad

  type 'a supported_functor_axioms = {
    Map_id: 'a,
    Map_comp: 'a,
    Supp_Map: 'a list,
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

  type supported_functor_model = {
    Map: term,
    Supps: term list,
    tacs: (Proof.context -> tactic) supported_functor_axioms
  };

  type bmv_monad_model = {
    ops: typ list,
    bd: term,
    var_class: class,
    bmv_ops: bmv_monad list,
    frees: typ list,
    leader: int,
    lives: typ list,
    lives': typ list,
    params: {
      model: supported_functor_model,
      Map_Sb: Proof.context -> tactic
    } option list,
    Injs: term list list,
    Sbs: term list,
    Vrs: term option list list list,
    tacs: (Proof.context -> tactic) bmv_monad_axioms list
  }

  val ops_of_bmv_monad: bmv_monad -> typ list;
  val bd_of_bmv_monad: bmv_monad -> term;
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

  val morph_bmv_monad: morphism -> bmv_monad -> bmv_monad;

  val bmv_monad_def: BNF_Def.inline_policy -> (Proof.context -> BNF_Def.fact_policy)
    -> (binding -> binding) -> bmv_monad_model -> local_theory -> bmv_monad * local_theory

  val compose_bmv_monad: (binding -> binding) -> bmv_monad -> bmv_monad list -> local_theory -> bmv_monad * local_theory
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

fun morph_bmv_axioms phi {
  Sb_Inj, Sb_comp_Injs, Sb_comp, Sb_cong, Vrs_bds, Vrs_Injs, Vrs_Sbs
} = {
  Sb_Inj = Morphism.thm phi Sb_Inj,
  Sb_comp_Injs = map (Morphism.thm phi) Sb_comp_Injs,
  Sb_comp = Morphism.thm phi Sb_comp,
  Sb_cong = Morphism.thm phi Sb_cong,
  Vrs_bds = map (map (Option.map (Morphism.thm phi))) Vrs_bds,
  Vrs_Injs = map (map (Option.map (Morphism.thm phi))) Vrs_Injs,
  Vrs_Sbs = map (map (Option.map (Morphism.thm phi))) Vrs_Sbs
} : thm bmv_monad_axioms

type 'a supported_functor_axioms = {
  Map_id: 'a,
  Map_comp: 'a,
  Supp_Map: 'a list,
  Map_cong: 'a
};

fun morph_supported_functor_axioms phi { Map_id, Map_comp, Supp_Map, Map_cong } = {
  Map_id = Morphism.thm phi Map_id,
  Map_comp = Morphism.thm phi Map_comp,
  Supp_Map = map (Morphism.thm phi) Supp_Map,
  Map_cong = Morphism.thm phi Map_cong
} : thm supported_functor_axioms;

type supported_functor_model = {
  Map: term,
  Supps: term list,
  tacs: (Proof.context -> tactic) supported_functor_axioms
};

datatype bmv_monad = BMV of {
  ops: typ list,
  bd: term,
  var_class: class,
  leader: int,
  frees: typ list,
  lives: typ list,
  lives': typ list,
  params: {
    Map: term,
    Supps: term list,
    axioms: thm supported_functor_axioms,
    Map_Sb: thm
  } option list,
  Injs: term list list,
  Sbs: term list,
  Vrs: term option list list list,
  axioms: thm bmv_monad_axioms list
}

fun morph_bmv_param phi { Map, Supps, axioms, Map_Sb } = {
  Map = Morphism.term phi Map,
  Supps = map (Morphism.term phi) Supps,
  axioms = morph_supported_functor_axioms phi axioms,
  Map_Sb = Morphism.thm phi Map_Sb
};

fun morph_bmv_monad phi (BMV {
  ops, bd, var_class, leader, frees, lives, lives', params, Injs, Sbs, Vrs, axioms
}) = BMV {
  ops = map (Morphism.typ phi) ops,
  bd = Morphism.term phi bd,
  leader = leader,
  var_class = var_class,
  frees = map (Morphism.typ phi) frees,
  lives = map (Morphism.typ phi) lives,
  lives' = map (Morphism.typ phi) lives',
  params = map (Option.map (morph_bmv_param phi)) params,
  Injs = map (map (Morphism.term phi)) Injs,
  Sbs = map (Morphism.term phi) Sbs,
  Vrs = map (map (map (Option.map (Morphism.term phi)))) Vrs,
  axioms = map (morph_bmv_axioms phi) axioms
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

type supported_functor_model = {
  Map: term,
  Supps: term list,
  tacs: (Proof.context -> tactic) supported_functor_axioms
};

fun morph_supported_functor_model phi { Map, Supps, tacs } = {
  Map = Morphism.term phi Map,
  Supps = map (Morphism.term phi) Supps,
  tacs = tacs
} : supported_functor_model;

type bmv_monad_model = {
  ops: typ list,
  bd: term,
  var_class: class,
  frees: typ list,
  lives: typ list,
  lives': typ list,
  params: {
    model: supported_functor_model,
    Map_Sb: Proof.context -> tactic
  } option list,
  bmv_ops: bmv_monad list,
  leader: int,
  Injs: term list list,
  Sbs: term list,
  Vrs: term option list list list,
  tacs: (Proof.context -> tactic) bmv_monad_axioms list
}

fun morph_bmv_monad_model phi ({ ops, bd, var_class, frees, lives, lives', params, bmv_ops, leader, Injs, Sbs, Vrs, tacs }: bmv_monad_model) = {
  ops = map (Morphism.typ phi) ops,
  bd = Morphism.term phi bd,
  var_class = var_class,
  frees = map (Morphism.typ phi) frees,
  lives = map (Morphism.typ phi) lives,
  lives' = map (Morphism.typ phi) lives',
  params = map (Option.map (fn { model, Map_Sb } => {
    model = morph_supported_functor_model phi model,
    Map_Sb = Map_Sb
  })) params,
  bmv_ops = map (morph_bmv_monad phi) bmv_ops,
  leader = leader,
  Injs = map (map (Morphism.term phi)) Injs,
  Sbs = map (Morphism.term phi) Sbs,
  Vrs = map (map (map (Option.map (Morphism.term phi)))) Vrs,
  tacs = tacs
} : bmv_monad_model;

val mk_small_prems = map2 (fn rho => fn Inj => HOLogic.mk_Trueprop (mk_ordLess
  (mk_card_of (HOLogic.mk_Collect ("a", fst (dest_funT (fastype_of Inj)),
    HOLogic.mk_not (HOLogic.mk_eq (rho $ Bound 0, Inj $ Bound 0))
  )))
  (mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of Inj)))))
));

fun prove_axioms (model: bmv_monad_model) lthy =
  let
    val Ts = #ops model @ maps ops_of_bmv_monad (#bmv_ops model);
    val Sbs = #Sbs model @ maps Sbs_of_bmv_monad (#bmv_ops model);
    val Injss = #Injs model @ maps Injs_of_bmv_monad (#bmv_ops model);
    val Vrss = #Vrs model @ maps Vrs_of_bmv_monad (#bmv_ops model);

    val axioms = @{map 5} (fn T => fn Injs => fn Sb => fn Vrs => fn tacs =>
      let
        val (own_Injs, other_Injs) = partition (fn Inj => member (op=) (#ops model) (body_type (fastype_of Inj))) Injs;
        val is_own_Inj = map (member (op=) (#ops model) o body_type o fastype_of) Injs;
        val other_idxs = map (fn Inj => find_index (fn T => body_type (fastype_of Inj) = T) Ts) other_Injs;
        val ((((rhos, rhos'), aa), x), _) = lthy
          |> mk_Frees "\<rho>" (map fastype_of Injs)
          ||>> mk_Frees "\<rho>'" (map fastype_of Injs)
          ||>> mk_Frees "a" (map (fst o dest_funT o fastype_of) Injs)
          ||>> apfst hd o mk_Frees "x" [T];
        val nown = length own_Injs;
        val (own_rhos, other_rhos) = chop nown rhos;
        val (own_rhos', other_rhos') = chop nown rhos';

        val Sb_Inj = Goal.prove_sorry lthy [] [] (
          mk_Trueprop_eq (Term.list_comb (Sb, Injs), HOLogic.id_const T)
        ) (fn {context=ctxt, ...} => #Sb_Inj tacs ctxt);

        val small_prems = mk_small_prems rhos Injs;
        val small_prems' = mk_small_prems rhos' Injs;

        val Sb_comp_Injs = @{map 3} (fn Inj => fn rho => fn tac => Goal.prove_sorry lthy [] [] (
          fold_rev Logic.all rhos (fold_rev (curry Logic.mk_implies) small_prems (mk_Trueprop_eq (
            HOLogic.mk_comp (Term.list_comb (Sb, rhos), Inj), rho
          )))
        ) (fn {context=ctxt, ...} => tac ctxt)) own_Injs own_rhos (#Sb_comp_Injs tacs);

        val Sb_comp = Goal.prove_sorry lthy [] [] (fold_rev Logic.all (rhos @ rhos') (
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
        )) (fn {context=ctxt, ...} => #Sb_comp tacs ctxt);

        val Vrs_bds = map2 (map2 (@{map_option 2} (fn Vrs => fn tac =>
          Goal.prove_sorry lthy [] [] (Logic.all x (HOLogic.mk_Trueprop (
            mk_ordLess (mk_card_of (Vrs $ x)) (#bd model)
          ))) (fn {context=ctxt, ...} => tac ctxt)
        ))) Vrs (#Vrs_bds tacs);

        val Vrs_Injs = @{map 3} (fn Inj => map2 (@{map_option 2} (fn tac => fn Vrs =>
          let
            val a = the (List.find (fn a => fastype_of a = hd (binder_types (fastype_of Inj))) aa);
            val T = HOLogic.dest_setT (body_type (fastype_of Vrs));
          in Goal.prove_sorry lthy [] [] (
            Logic.all a (mk_Trueprop_eq (
              Vrs $ (Inj $ a),
              if fastype_of a = T then mk_singleton a else mk_bot T))
          ) (fn {context=ctxt, ...} => tac ctxt) end))) own_Injs (#Vrs_Injs tacs) (cond_keep Vrs is_own_Inj);

        val Vrs_Sbs = @{map 3} (fn rho => map2 (@{map_option 2} (fn Vrs => fn tac =>
          let
            val var = HOLogic.dest_setT (body_type (fastype_of Vrs));
            val idx = find_index (fn T => body_type (fastype_of rho) = T) Ts;
            val idx' = find_index (fn t => fastype_of t = fastype_of rho) (nth Injss idx);
            val Vrs' = hd (map_filter (Option.mapPartial (fn t =>
              if HOLogic.dest_setT (body_type (fastype_of t)) = var then SOME t else NONE
            )) (nth (nth Vrss idx) idx'));

            val goal = fold_rev Logic.all (rhos @ [x]) (
              fold_rev (curry Logic.mk_implies) small_prems (mk_Trueprop_eq (
                Vrs $ (Term.list_comb (Sb, rhos) $ x),
                mk_UNION (Vrs $ x) (Term.abs ("a", var) (Vrs' $ (rho $ Bound 0)))
              ))
            );
          in Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, ...} => tac ctxt) end
        ))) rhos Vrs (#Vrs_Sbs tacs);

        val Sb_cong = Goal.prove_sorry lthy [] [] (fold_rev Logic.all (rhos @ rhos' @ [x]) (
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
        ))) (fn {context=ctxt, ...} => #Sb_cong tacs ctxt);

      in {
        Sb_Inj = Sb_Inj,
        Sb_comp_Injs = Sb_comp_Injs,
        Sb_comp = Sb_comp,
        Vrs_Injs = Vrs_Injs,
        Vrs_bds = Vrs_bds,
        Vrs_Sbs = Vrs_Sbs,
        Sb_cong = Sb_cong
      } : thm bmv_monad_axioms end
    ) (#ops model) (#Injs model) (#Sbs model) (#Vrs model) (#tacs model);
  in axioms end;

fun prove_params (model: bmv_monad_model) lthy = @{map 4} (fn T => fn Sb => fn Injs => Option.map (fn param =>
  let
    val (Cs, _) = lthy
      |> mk_TFrees (length (#lives model));
    val ((((fs, gs), rhos), x), _) = lthy
      |> mk_Frees "f" (map2 (curry (op-->)) (#lives model) (#lives' model))
      ||>> mk_Frees "g" (map2 (curry (op-->)) (#lives' model) Cs)
      ||>> mk_Frees "\<rho>" (map fastype_of Injs)
      ||>> apfst hd o mk_Frees "x" [T];
    val pmodel = #model param;

    val Map_id = Goal.prove_sorry lthy [] [] (Term.subst_atomic_types (#lives' model ~~ #lives model) (
      mk_Trueprop_eq (
        Term.list_comb (#Map pmodel, map HOLogic.id_const (#lives model)), HOLogic.id_const T
      )
    )) (fn {context=ctxt, ...} => #Map_id (#tacs pmodel) ctxt);

    val Map_comp = Goal.prove_sorry lthy [] [] (fold_rev Logic.all (fs @ gs) (mk_Trueprop_eq (
      HOLogic.mk_comp (Term.list_comb (
        Term.subst_atomic_types ((#lives model @ #lives' model) ~~ (#lives' model @ Cs)) (#Map pmodel), gs
      ), Term.list_comb (#Map pmodel, fs)),
      Term.list_comb (Term.subst_atomic_types (#lives' model ~~ Cs) (#Map pmodel), map2 (curry HOLogic.mk_comp) gs fs)
    ))) (fn {context=ctxt, ...} => #Map_comp (#tacs pmodel) ctxt);

    val Supp_Maps = @{map 3} (fn Supp => fn f => fn tac =>
      Goal.prove_sorry lthy [] [] (fold_rev Logic.all (fs @ [x]) (mk_Trueprop_eq (
        Term.subst_atomic_types (#lives model ~~ #lives' model) Supp $ (Term.list_comb (#Map pmodel, fs) $ x),
        mk_image f $ (Supp $ x)
      ))) (fn {context=ctxt, ...} => tac ctxt)
    ) (#Supps pmodel) fs (#Supp_Map (#tacs pmodel));

    val (gs', _) = lthy
      |> mk_Frees "g" (map fastype_of fs);
    val Map_cong = Goal.prove_sorry lthy [] [] (fold_rev Logic.all (fs @ gs' @ [x]) (
      fold_rev (curry Logic.mk_implies) (@{map 3} (fn Supp => fn f => fn g =>
        let val a = Free ("a", hd (binder_types (fastype_of f)));
        in Logic.all a (Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Supp $ x)),
          mk_Trueprop_eq (f $ a, g $ a)
        )) end
      ) (#Supps pmodel) fs gs') (mk_Trueprop_eq (
        Term.list_comb (#Map pmodel, fs) $ x,
        Term.list_comb (#Map pmodel, gs') $ x
      )))) (fn {context=ctxt, ...} => #Map_cong (#tacs pmodel) ctxt);

    val Map_Sb = Goal.prove_sorry lthy [] [] (fold_rev Logic.all (fs @ rhos) (
      fold_rev (curry Logic.mk_implies) (mk_small_prems rhos Injs) (mk_Trueprop_eq (
        HOLogic.mk_comp (Term.list_comb (#Map pmodel, fs), Term.list_comb (Sb, rhos)),
        HOLogic.mk_comp (Term.list_comb (
          Term.subst_atomic_types (#lives model ~~ #lives' model) Sb, rhos
        ), Term.list_comb (#Map pmodel, fs))
      ))
    )) (fn {context=ctxt, ...} => #Map_Sb param ctxt);
  in {
    Map = #Map pmodel,
    Supps = #Supps pmodel,
    axioms = {
      Map_id = Map_id,
      Map_comp = Map_comp,
      Supp_Map = Supp_Maps,
      Map_cong = Map_cong
    },
    Map_Sb = Map_Sb
  } end
)) (#ops model) (#Sbs model) (#Injs model) (#params model);

fun bmv_monad_def inline_policy fact_policy qualify (model: bmv_monad_model) lthy =
  let
    val _ = let
      val var_large = MRBNF_Def.get_class_assumption [#var_class model] "large" lthy;
      val bd' = snd (dest_comb (dest_card_of (
        fst (dest_ordLeq (HOLogic.dest_Trueprop (Thm.prop_of var_large)))
      )));
      in if bd' <> #bd model then error "var_class does not match bound" else () end

    val frees = map (fn T => TFree (apsnd (
      Sign.minimize_sort (Proof_Context.theory_of lthy) o cons (#var_class model)
    ) (dest_TFree T))) (#frees model);
    val model = morph_bmv_monad_model (MRBNF_Util.subst_typ_morphism (#frees model ~~ frees)) model;

    val axioms = prove_axioms model lthy;
    val params = prove_params model lthy;

    val bmv = BMV {
      ops = #ops model @ maps (#ops o Rep_bmv) (#bmv_ops model),
      bd = #bd model,
      var_class = #var_class model,
      leader = #leader model,
      frees = #frees model,
      lives = #lives model,
      lives' = #lives' model,
      params = params,
      Injs = #Injs model @ maps (#Injs o Rep_bmv) (#bmv_ops model),
      Sbs = #Sbs model @ maps (#Sbs o Rep_bmv) (#bmv_ops model),
      Vrs = #Vrs model @ maps (#Vrs o Rep_bmv) (#bmv_ops model),
      axioms = axioms @ maps (#axioms o Rep_bmv) (#bmv_ops model)
    } : bmv_monad;
  in (bmv, lthy) end

(* Cleanup: Throw away op iff any:
- not the leader
- does not appear in the codomain of any (=of any **other** SOp) Injection,
*)

fun compose_bmv_monad qualify outer inners lthy =
  let
    val _ = if length (lives_of_bmv_monad outer) <> length inners then
      error "Outer needs exactly as many lives as there are inners" else ()

    val ops' = map (Term.typ_subst_atomic (lives_of_bmv_monad outer ~~ map (fn bmv =>
      nth (ops_of_bmv_monad bmv) (leader_of_bmv_monad bmv)
    ) inners)) (ops_of_bmv_monad outer);

    val _ = @{print} ops'
  in error "unfinished" end;

end