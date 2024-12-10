signature BMV_MONAD_DEF = sig
  type bmv_monad

  type 'a bmv_monad_axioms = {
    Sb_Inj: 'a,
    Sb_comp_Injs: 'a list,
    Sb_comp: 'a,
    Sb_cong: 'a,
    Vrs_Injs: 'a list,
    Vrs_Sbs: 'a list
  };

  type bmv_monad_model = {
    ops: typ list,
    bmv_ops: bmv_monad list,
    frees: typ list,
    lives: typ list,
    leader: int,
    Injs: (term list * (term * int) list) list,
    Sbs: term list,
    Maps: term option list,
    Vrs: term list list,
    tacs: (Proof.context -> tactic) bmv_monad_axioms list
  }

  val ops_of_bmv_monad: bmv_monad -> typ list;
  val leader_of_bmv_monad: bmv_monad -> int;
  val frees_of_bmv_monad: bmv_monad -> typ list;
  val lives_of_bmv_monad: bmv_monad -> typ list;
  val Injs_of_bmv_monad: bmv_monad -> term list list;
  val Sbs_of_bmv_monad: bmv_monad -> term list;
  val Maps_of_bmv_monad: bmv_monad -> term option list;
  val Vrs_of_bmv_monad: bmv_monad -> term list list;

  val morph_bmv_monad: morphism -> bmv_monad -> bmv_monad;

  val bmv_monad_def: BNF_Def.inline_policy -> (Proof.context -> BNF_Def.fact_policy)
    -> (binding -> binding) -> bmv_monad_model -> local_theory -> bmv_monad
end

structure BMV_Monad_Def : BMV_MONAD_DEF = struct

open MRBNF_Util

type 'a bmv_monad_axioms = {
  Sb_Inj: 'a,
  Sb_comp_Injs: 'a list,
  Sb_comp: 'a,
  Sb_cong: 'a,
  Vrs_Injs: 'a list,
  Vrs_Sbs: 'a list
};

fun morph_bmv_axioms phi {
  Sb_Inj, Sb_comp_Injs, Sb_comp, Sb_cong, Vrs_Injs, Vrs_Sbs
} = {
  Sb_Inj = Morphism.thm phi Sb_Inj,
  Sb_comp_Injs = map (Morphism.thm phi) Sb_comp_Injs,
  Sb_comp = Morphism.thm phi Sb_comp,
  Sb_cong = Morphism.thm phi Sb_cong,
  Vrs_Injs = map (Morphism.thm phi) Vrs_Injs,
  Vrs_Sbs = map (Morphism.thm phi) Vrs_Sbs
} : thm bmv_monad_axioms

datatype bmv_monad = BMV of {
  ops: typ list,
  leader: int,
  frees: typ list,
  lives: typ list,
  Injs: term list list,
  Sbs: term list,
  Maps: term option list,
  Vrs: term list list,
  axioms: thm bmv_monad_axioms list
}

fun Rep_bmv (BMV x) = x

val ops_of_bmv_monad = #ops o Rep_bmv
val leader_of_bmv_monad = #leader o Rep_bmv
val frees_of_bmv_monad = #frees o Rep_bmv
val lives_of_bmv_monad = #lives o Rep_bmv
val Injs_of_bmv_monad = #Injs o Rep_bmv
val Sbs_of_bmv_monad = #Sbs o Rep_bmv
val Maps_of_bmv_monad = #Maps o Rep_bmv
val Vrs_of_bmv_monad = #Vrs o Rep_bmv

type bmv_monad_model = {
  ops: typ list,
  frees: typ list,
  lives: typ list,
  bmv_ops: bmv_monad list,
  leader: int,
  Injs: (term list * (term * int) list) list,
  Sbs: term list,
  Maps: term option list,
  Vrs: term list list,
  tacs: (Proof.context -> tactic) bmv_monad_axioms list
}

fun morph_bmv_monad phi (BMV {
  ops, leader, frees, lives, Injs, Sbs, Maps, Vrs, axioms
}) = BMV {
  ops = map (Morphism.typ phi) ops,
  leader = leader,
  frees = map (Morphism.typ phi) frees,
  lives = map (Morphism.typ phi) lives,
  Injs = map (map (Morphism.term phi)) Injs,
  Sbs = map (Morphism.term phi) Sbs,
  Maps = map (Option.map (Morphism.term phi)) Maps,
  Vrs = map (map (Morphism.term phi)) Vrs,
  axioms = map (morph_bmv_axioms phi) axioms
}

fun prove_axioms (model: bmv_monad_model) lthy =
  let
    val Ts = #ops model @ maps ops_of_bmv_monad (#bmv_ops model);
    val Sbs = #Sbs model @ maps Sbs_of_bmv_monad (#bmv_ops model);
    val Injss = #Injs model @ map (rpair []) (maps Injs_of_bmv_monad (#bmv_ops model));
    val Vrss = #Vrs model @ maps Vrs_of_bmv_monad (#bmv_ops model);

    val axioms = @{map 5} (fn T => fn (own_Injs, other_Injs) => fn Sb => fn Vrs => fn tacs =>
      let
        val (other_Injs, other_idxs) = split_list other_Injs;
        val Injs = own_Injs @ other_Injs;
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

        fun mk_small_prems rhos = map2 (fn rho => fn Inj => HOLogic.mk_Trueprop (mk_ordLess
          (mk_card_of (HOLogic.mk_Collect ("a", fst (dest_funT (fastype_of Inj)),
            HOLogic.mk_not (HOLogic.mk_eq (rho $ Bound 0, Inj $ Bound 0))
          )))
          (mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of Inj)))))
        )) rhos Injs;
        val small_prems = mk_small_prems rhos;
        val small_prems' = mk_small_prems rhos';

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
              ) (fst Injs @ map fst (snd Injs))), rho)
            ) other_rhos (map (nth Sbs) other_idxs) (map (nth Injss) other_idxs))
          ))
        )) (fn {context=ctxt, ...} => #Sb_comp tacs ctxt);

        val Vrs_Injs = @{map 4} (fn Vrs => fn Inj => fn a => fn tac => Goal.prove_sorry lthy [] [] (
          Logic.all a (mk_Trueprop_eq (Vrs $ (Inj $ a), mk_singleton a))
        ) (fn {context=ctxt, ...} => tac ctxt)) (take nown Vrs) own_Injs (take nown aa) (#Vrs_Injs tacs);

        val Vrs_Sbs = map2 (fn Vr => fn tac => Goal.prove_sorry lthy [] [] (fold_rev Logic.all (rhos @ [x]) (
          fold_rev (curry Logic.mk_implies) small_prems (mk_Trueprop_eq (
            Vr $ (Term.list_comb (Sb, rhos) $ x),
            foldl1 mk_Un (@{map_filter 2} (fn rho => Option.map (fn Vrs' => mk_UNION (Vr $ x) (
              Term.abs ("a", HOLogic.dest_setT (snd (dest_funT (fastype_of Vrs')))) (
                Vrs' $ (rho $ Bound 0)
              )
            ))) rhos (map SOME (take nown Vrs) @ map (fn idx =>
              List.find (fn t => body_type (fastype_of t) = body_type (fastype_of Vr)) (nth Vrss idx)
            ) other_idxs))
          ))
        )) (fn {context=ctxt, ...} => tac ctxt)) Vrs (#Vrs_Sbs tacs);

        val Sb_cong = Goal.prove_sorry lthy [] [] (fold_rev Logic.all (rhos @ rhos' @ [x]) (
          fold_rev (curry Logic.mk_implies) (small_prems @ small_prems' @ @{map 4} (fn rho => fn rho' => fn Vrs => fn a =>
            Logic.all a (Logic.mk_implies (
              HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Vrs $ x)),
              mk_Trueprop_eq (rho $ a, rho' $ a)
            ))
          ) rhos rhos' Vrs aa) (mk_Trueprop_eq (
            Term.list_comb (Sb, rhos) $ x,
            Term.list_comb (Sb, rhos') $ x
          )
        ))) (fn {context=ctxt, ...} => #Sb_cong tacs ctxt);

      in {
        Sb_Inj = Sb_Inj,
        Sb_comp_Injs = Sb_comp_Injs,
        Sb_comp = Sb_comp,
        Vrs_Injs = Vrs_Injs,
        Vrs_Sbs = Vrs_Sbs,
        Sb_cong = Sb_cong
      } end
    ) (#ops model) (#Injs model) (#Sbs model) (#Vrs model) (#tacs model);
  in axioms end;

fun bmv_monad_def inline_policy fact_policy qualify (model: bmv_monad_model) lthy =
  let
    val axioms = prove_axioms model lthy;

    val bmv = BMV {
      ops = #ops model @ maps (#ops o Rep_bmv) (#bmv_ops model),
      leader = #leader model,
      frees = #frees model,
      lives = #lives model,
      Injs = map (fn (xs, ys) => xs @ map fst ys) (#Injs model) @ maps (#Injs o Rep_bmv) (#bmv_ops model),
      Sbs = #Sbs model @ maps (#Sbs o Rep_bmv) (#bmv_ops model),
      Vrs = #Vrs model @ maps (#Vrs o Rep_bmv) (#bmv_ops model),
      Maps = #Maps model @ maps (#Maps o Rep_bmv) (#bmv_ops model),
      axioms = axioms @ maps (#axioms o Rep_bmv) (#bmv_ops model)
    } : bmv_monad;
  in bmv end

end