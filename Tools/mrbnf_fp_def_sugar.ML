signature MRBNF_FP_DEF_SUGAR =
sig
  type 'a fp_result_T = {
    T: typ,
    ctor: term,
    rename: term,
    FVars: term list,
    inner: 'a,

    inject: thm,
    rename_id0: thm,
    rename_id: thm,
    rename_comp0: thm,
    rename_comp: thm,
    rename_bij: thm,
    rename_inv_simp: thm,
    FVars_ctors: thm list,
    FVars_renames: thm list,
    card_of_FVars_bounds: thm list
  };

  type raw_result = {
    alpha: term,

    alpha_refl: thm,
    alpha_sym: thm,
    alpha_trans: thm,
    alpha_bij: thm,
    alpha_bij_eq: thm,
    alpha_FVarss: thm list,

    subshapes: term list option,
    wf_subshapes: thm list option,
    set_subshapess: thm list list option,
    set_subshape_imagess: thm list list option,
    subshape_induct: thm option
  };

  type quotient_result = {
    abs: term,
    rep: term,

    alpha_quotient_sym: thm,
    total_abs_eq_iff: thm,
    abs_rep: thm,
    rep_abs: thm
  };

  type fp_result = {
    fp: BNF_Util.fp_kind,
    bound_vars: typ list,
    binding_relation: int list,
    raw_fp: raw_result fp_result_T,
    quotient_fp: quotient_result fp_result_T,
    pre_mrbnf: MRBNF_Def.mrbnf
  };

  val morph_fp_result_T: (morphism -> 'a -> 'a) -> morphism -> 'a fp_result_T -> 'a fp_result_T
  val morph_raw_result: morphism -> raw_result -> raw_result
  val morph_quotient_result: morphism -> quotient_result -> quotient_result
  val morph_fp_result: morphism -> fp_result -> fp_result

  val fp_result_of: Proof.context -> string -> fp_result option
  val register_fp_results: fp_result list -> local_theory -> local_theory

end;

structure MRBNF_FP_Def_Sugar : MRBNF_FP_DEF_SUGAR =
struct

type 'a fp_result_T = {
  T: typ,
  ctor: term,
  rename: term,
  FVars: term list,
  inner: 'a,

  inject: thm,
  rename_id0: thm,
  rename_id: thm,
  rename_comp0: thm,
  rename_comp: thm,
  rename_bij: thm,
  rename_inv_simp: thm,
  FVars_ctors: thm list,
  FVars_renames: thm list,
  card_of_FVars_bounds: thm list
};

fun morph_fp_result_T morph phi { T, ctor, rename, FVars, inner, inject, rename_id0, rename_id,
  rename_comp0, rename_comp, rename_bij, rename_inv_simp, FVars_ctors, FVars_renames, card_of_FVars_bounds } = {
  T = Morphism.typ phi T,
  ctor = Morphism.term phi ctor,
  rename = Morphism.term phi rename,
  FVars = map (Morphism.term phi) FVars,
  inner = morph phi inner,
  inject = Morphism.thm phi inject,
  rename_id0 = Morphism.thm phi rename_id0,
  rename_id = Morphism.thm phi rename_id,
  rename_comp0 = Morphism.thm phi rename_comp0,
  rename_comp = Morphism.thm phi rename_comp,
  rename_bij = Morphism.thm phi rename_bij,
  rename_inv_simp = Morphism.thm phi rename_inv_simp,
  FVars_ctors = map (Morphism.thm phi) FVars_ctors,
  FVars_renames = map (Morphism.thm phi) FVars_renames,
  card_of_FVars_bounds = map (Morphism.thm phi) card_of_FVars_bounds
} : 'a fp_result_T;

type raw_result = {
  alpha: term,

  alpha_refl: thm,
  alpha_sym: thm,
  alpha_trans: thm,
  alpha_bij: thm,
  alpha_bij_eq: thm,
  alpha_FVarss: thm list,

  subshapes: term list option,
  wf_subshapes: thm list option,
  set_subshapess: thm list list option,
  set_subshape_imagess: thm list list option,
  subshape_induct: thm option
};

fun morph_raw_result phi { alpha, alpha_refl, alpha_sym, alpha_trans, alpha_bij, alpha_bij_eq,
  alpha_FVarss, subshapes, wf_subshapes, set_subshapess, set_subshape_imagess, subshape_induct } = {
  alpha = Morphism.term phi alpha,
  alpha_refl = Morphism.thm phi alpha_refl,
  alpha_sym = Morphism.thm phi alpha_sym,
  alpha_trans = Morphism.thm phi alpha_trans,
  alpha_bij = Morphism.thm phi alpha_bij,
  alpha_bij_eq = Morphism.thm phi alpha_bij_eq,
  alpha_FVarss = map (Morphism.thm phi) alpha_FVarss,
  subshapes = Option.map (map (Morphism.term phi)) subshapes,
  wf_subshapes = Option.map (map (Morphism.thm phi)) wf_subshapes,
  set_subshapess = Option.map (map (map (Morphism.thm phi))) set_subshapess,
  set_subshape_imagess = Option.map (map (map (Morphism.thm phi))) set_subshape_imagess,
  subshape_induct = Option.map (Morphism.thm phi) subshape_induct
} : raw_result;

type quotient_result = {
  abs: term,
  rep: term,

  alpha_quotient_sym: thm,
  total_abs_eq_iff: thm,
  abs_rep: thm,
  rep_abs: thm
};

fun morph_quotient_result phi { abs, rep, alpha_quotient_sym, total_abs_eq_iff, abs_rep, rep_abs } = {
  abs = Morphism.term phi abs,
  rep = Morphism.term phi rep,
  alpha_quotient_sym = Morphism.thm phi alpha_quotient_sym,
  total_abs_eq_iff = Morphism.thm phi total_abs_eq_iff,
  abs_rep = Morphism.thm phi abs_rep,
  rep_abs = Morphism.thm phi rep_abs
} : quotient_result;

type fp_result = {
  fp: BNF_Util.fp_kind,
  bound_vars: typ list,
  binding_relation: int list,
  raw_fp: raw_result fp_result_T,
  quotient_fp: quotient_result fp_result_T,
  pre_mrbnf: MRBNF_Def.mrbnf
};

fun morph_fp_result phi ({ fp, binding_relation, bound_vars, raw_fp, quotient_fp, pre_mrbnf }) = {
  fp = fp, binding_relation = binding_relation,
  bound_vars = map (Morphism.typ phi) bound_vars,
  raw_fp = morph_fp_result_T morph_raw_result phi raw_fp,
  quotient_fp = morph_fp_result_T morph_quotient_result phi quotient_fp,
  pre_mrbnf = MRBNF_Def.morph_mrbnf phi pre_mrbnf
} : fp_result;

structure Data = Generic_Data (
  type T = fp_result Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
);

val register_fp_results = fold (fn fp_result as { quotient_fp = { T = Type (s, _), ...}, ...} =>
  Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (Symtab.update (s, morph_fp_result phi fp_result))));

fun fp_result_of_generic context =
  Option.map (morph_fp_result (Morphism.transfer_morphism (Context.theory_of context)))
  o Symtab.lookup (Data.get context);

val fp_result_of = fp_result_of_generic o Context.Proof;

end;