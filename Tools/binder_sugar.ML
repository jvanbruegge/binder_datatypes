signature BINDER_SUGAR = sig

type binder_sugar = {
  map_simps: thm list,
  set_simpss: thm list list,
  permute_simps: thm list,
  map_permute: thm,
  subst_simps: thm list option,
  IImsupp_permute_commutes: thm list option,
  IImsupp_Diffs: thm list option,
  tvsubst_permute: thm option,
  bsetss: term option list list,
  bset_bounds: thm list,
  mrbnf: MRBNF_Def.mrbnf,
  strong_induct: thm option,
  distinct: thm list,
  inject: thm list,
  ctors: (term * thm) list
};

val morph_binder_sugar: morphism -> binder_sugar -> binder_sugar;


val binder_sugar_of: local_theory -> string -> binder_sugar option
val register_binder_sugar: string -> binder_sugar -> local_theory -> local_theory

end

structure Binder_Sugar : BINDER_SUGAR = struct

type binder_sugar = {
  map_simps: thm list,
  set_simpss: thm list list,
  permute_simps: thm list,
  map_permute: thm,
  subst_simps: thm list option,
  IImsupp_permute_commutes: thm list option,
  IImsupp_Diffs: thm list option,
  tvsubst_permute: thm option,
  bsetss: term option list list,
  bset_bounds: thm list,
  mrbnf: MRBNF_Def.mrbnf,
  strong_induct: thm option,
  distinct: thm list,
  inject: thm list,
  ctors: (term * thm) list
};

fun morph_binder_sugar phi { map_simps, permute_simps, map_permute, set_simpss, subst_simps, mrbnf,
  strong_induct, distinct, inject, ctors, bsetss, bset_bounds, IImsupp_permute_commutes, IImsupp_Diffs,
  tvsubst_permute
} = {
  map_simps = map (Morphism.thm phi) map_simps,
  permute_simps = map (Morphism.thm phi) permute_simps,
  map_permute = Morphism.thm phi map_permute,
  set_simpss = map (map (Morphism.thm phi)) set_simpss,
  subst_simps = Option.map (map (Morphism.thm phi)) subst_simps,
  IImsupp_permute_commutes = Option.map (map (Morphism.thm phi)) IImsupp_permute_commutes,
  IImsupp_Diffs = Option.map (map (Morphism.thm phi)) IImsupp_Diffs,
  tvsubst_permute = Option.map (Morphism.thm phi) tvsubst_permute,
  bsetss = map (map (Option.map (Morphism.term phi))) bsetss,
  bset_bounds = map (Morphism.thm phi) bset_bounds,
  mrbnf = MRBNF_Def.morph_mrbnf phi mrbnf,
  strong_induct = Option.map (Morphism.thm phi) strong_induct,
  distinct = map (Morphism.thm phi) distinct,
  inject = map (Morphism.thm phi) inject,
  ctors = map (MRBNF_Util.map_prod (Morphism.term phi) (Morphism.thm phi)) ctors
} : binder_sugar;

structure Data = Generic_Data (
  type T = binder_sugar Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
);

fun register_binder_sugar name sugar =
  Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
    (fn phi => Data.map (Symtab.update (name, morph_binder_sugar phi sugar)));

fun binder_sugar_of_generic context =
  Option.map (morph_binder_sugar (Morphism.transfer_morphism (Context.theory_of context)))
  o Symtab.lookup (Data.get context);

val binder_sugar_of = binder_sugar_of_generic o Context.Proof;

end