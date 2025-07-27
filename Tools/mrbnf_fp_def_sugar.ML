signature MRBNF_FP_DEF_SUGAR =
sig
  type 'a fp_result_T = {
    T: typ,
    ctor: term,
    permute: term,
    FVarss: term list,
    noclash: term * thm,
    inner: 'a,

    inject: thm,
    permute_ctor: thm,
    permute_id0: thm,
    permute_id: thm,
    permute_comp0: thm,
    permute_comp: thm,
    FVars_ctors: thm list,
    FVars_permutes: thm list,
    FVars_intross: thm list list,
    card_of_FVars_bounds: thm list,
    card_of_FVars_bound_UNIVs: thm list
  };

  type raw_result = {
    alpha: term,
    exhaust: thm,

    alpha_refl: thm,
    alpha_sym: thm,
    alpha_trans: thm,
    alpha_bij: thm,
    alpha_bij_eq: thm,
    alpha_bij_eq_inv: thm,
    alpha_FVarss: thm list,
    alpha_intro: thm,
    alpha_elim: thm
  };

  type quotient_result = {
    abs: term,
    rep: term,

    ctor_def: thm,
    permute_def: thm,
    FVars_defs: thm list,

    fresh_cases: thm,
    noclash_permute: thm,
    nnoclash_noclash: thm,
    total_abs_eq_iff: thm,
    abs_rep: thm,
    rep_abs: thm,
    rep_abs_sym: thm,
    abs_ctor: thm,

    permute_abs: thm,
    permute_cong: thm,
    permute_cong_id: thm,
    permute_bij: thm,
    permute_inv_simp: thm
  };

  type least_fp_thms = {
    subshape_rel: term,
    subshapess: term list list,
    wf_subshape: thm,
    set_subshapess: thm list list,
    set_subshape_permutess: thm list list,
    subshape_induct: thm,
    existential_induct: thm,
    fresh_induct_param: thm,
    fresh_induct: thm
  };

  type greatest_fp_thms = {
    existential_coinduct: thm,
    fresh_coinduct_param: thm
  };

  type fp_result = {
    fp: BNF_Util.fp_kind,
    binding_relation: int list list list,
    rec_vars: int list,
    bfree_vars: int list,
    raw_fps: raw_result fp_result_T list,
    quotient_fps: quotient_result fp_result_T list,
    fp_thms: (least_fp_thms, greatest_fp_thms) MRBNF_Util.either option,
    pre_mrbnfs: MRBNF_Def.mrbnf list
  };

  val substitute_vars: (typ * typ) list -> fp_result -> fp_result

  val morph_fp_result_T: (morphism -> 'a -> 'a) -> morphism -> 'a fp_result_T -> 'a fp_result_T
  val morph_raw_result: morphism -> raw_result -> raw_result
  val morph_quotient_result: morphism -> quotient_result -> quotient_result
  val morph_fp_result: morphism -> fp_result -> fp_result

  val fp_result_of: Proof.context -> string -> fp_result option
  val register_fp_results: fp_result list -> local_theory -> local_theory
  val note_fp_result: fp_result -> local_theory -> local_theory

end;

structure MRBNF_FP_Def_Sugar : MRBNF_FP_DEF_SUGAR =
struct

type 'a fp_result_T = {
  T: typ,
  ctor: term,
  permute: term,
  FVarss: term list,
  noclash: term * thm,
  inner: 'a,

  inject: thm,
  permute_ctor: thm,
  permute_id0: thm,
  permute_id: thm,
  permute_comp0: thm,
  permute_comp: thm,
  FVars_ctors: thm list,
  FVars_permutes: thm list,
  FVars_intross: thm list list,
  card_of_FVars_bounds: thm list,
  card_of_FVars_bound_UNIVs: thm list
};

fun morph_fp_result_T morph phi { T, ctor, permute, FVarss, noclash, inner, inject, permute_ctor,
  permute_id0, permute_id, permute_comp0, permute_comp, FVars_ctors, FVars_permutes, FVars_intross,
  card_of_FVars_bounds, card_of_FVars_bound_UNIVs } = {
  T = Morphism.typ phi T,
  ctor = Morphism.term phi ctor,
  permute = Morphism.term phi permute,
  FVarss = map (Morphism.term phi) FVarss,
  noclash = BNF_Util.map_prod (Morphism.term phi) (Morphism.thm phi) noclash,
  inner = morph phi inner,
  inject = Morphism.thm phi inject,
  permute_ctor = Morphism.thm phi permute_ctor,
  permute_id0 = Morphism.thm phi permute_id0,
  permute_id = Morphism.thm phi permute_id,
  permute_comp0 = Morphism.thm phi permute_comp0,
  permute_comp = Morphism.thm phi permute_comp,
  FVars_ctors = map (Morphism.thm phi) FVars_ctors,
  FVars_permutes = map (Morphism.thm phi) FVars_permutes,
  FVars_intross = map (map (Morphism.thm phi)) FVars_intross,
  card_of_FVars_bounds = map (Morphism.thm phi) card_of_FVars_bounds,
  card_of_FVars_bound_UNIVs = map (Morphism.thm phi) card_of_FVars_bound_UNIVs
} : 'a fp_result_T;

type raw_result = {
  alpha: term,
  exhaust: thm,

  alpha_refl: thm,
  alpha_sym: thm,
  alpha_trans: thm,
  alpha_bij: thm,
  alpha_bij_eq: thm,
  alpha_bij_eq_inv: thm,
  alpha_FVarss: thm list,
  alpha_intro: thm,
  alpha_elim: thm
};

fun morph_raw_result phi { alpha, exhaust, alpha_refl, alpha_sym, alpha_trans, alpha_bij,
  alpha_bij_eq, alpha_bij_eq_inv, alpha_FVarss, alpha_intro, alpha_elim } = {
  alpha = Morphism.term phi alpha,
  exhaust = Morphism.thm phi exhaust,
  alpha_refl = Morphism.thm phi alpha_refl,
  alpha_sym = Morphism.thm phi alpha_sym,
  alpha_trans = Morphism.thm phi alpha_trans,
  alpha_bij = Morphism.thm phi alpha_bij,
  alpha_bij_eq = Morphism.thm phi alpha_bij_eq,
  alpha_bij_eq_inv = Morphism.thm phi alpha_bij_eq_inv,
  alpha_FVarss = map (Morphism.thm phi) alpha_FVarss,
  alpha_intro = Morphism.thm phi alpha_intro,
  alpha_elim = Morphism.thm phi alpha_elim
} : raw_result;

type quotient_result = {
  abs: term,
  rep: term,

  ctor_def: thm,
  permute_def: thm,
  FVars_defs: thm list,

  fresh_cases: thm,
  nnoclash_noclash: thm,
  noclash_permute: thm,
  total_abs_eq_iff: thm,
  abs_rep: thm,
  rep_abs: thm,
  rep_abs_sym: thm,
  abs_ctor: thm,

  permute_abs: thm,
  permute_cong: thm,
  permute_cong_id: thm,
  permute_bij: thm,
  permute_inv_simp: thm
};

fun morph_quotient_result phi { abs, rep, ctor_def, permute_def, FVars_defs, nnoclash_noclash,
  total_abs_eq_iff, abs_rep, rep_abs, rep_abs_sym, abs_ctor, permute_cong, permute_cong_id,
  permute_bij, permute_inv_simp, noclash_permute, fresh_cases, permute_abs } = {
  abs = Morphism.term phi abs,
  rep = Morphism.term phi rep,
  ctor_def = Morphism.thm phi ctor_def,
  permute_def = Morphism.thm phi permute_def,
  FVars_defs = map (Morphism.thm phi) FVars_defs,
  fresh_cases = Morphism.thm phi fresh_cases,
  noclash_permute = Morphism.thm phi noclash_permute,
  nnoclash_noclash = Morphism.thm phi nnoclash_noclash,
  total_abs_eq_iff = Morphism.thm phi total_abs_eq_iff,
  abs_rep = Morphism.thm phi abs_rep,
  rep_abs = Morphism.thm phi rep_abs,
  rep_abs_sym = Morphism.thm phi rep_abs_sym,
  abs_ctor = Morphism.thm phi abs_ctor,
  permute_cong = Morphism.thm phi permute_cong,
  permute_cong_id = Morphism.thm phi permute_cong_id,
  permute_bij = Morphism.thm phi permute_bij,
  permute_inv_simp = Morphism.thm phi permute_inv_simp,
  permute_abs = Morphism.thm phi permute_abs
} : quotient_result;

type least_fp_thms = {
  subshape_rel: term,
  subshapess: term list list,
  wf_subshape: thm,
  set_subshapess: thm list list,
  set_subshape_permutess: thm list list,
  subshape_induct: thm,
  existential_induct: thm,
  fresh_induct_param: thm,
  fresh_induct: thm
};

fun morph_least_fp_thms phi ({ subshape_rel, subshapess, wf_subshape, set_subshapess,
  set_subshape_permutess, subshape_induct, existential_induct, fresh_induct_param, fresh_induct }) = {
  subshape_rel = Morphism.term phi subshape_rel,
  subshapess = map (map (Morphism.term phi)) subshapess,
  wf_subshape = Morphism.thm phi wf_subshape,
  set_subshapess = map (map (Morphism.thm phi)) set_subshapess,
  set_subshape_permutess = map (map (Morphism.thm phi)) set_subshape_permutess,
  subshape_induct = Morphism.thm phi subshape_induct,
  existential_induct = Morphism.thm phi existential_induct,
  fresh_induct_param = Morphism.thm phi fresh_induct_param,
  fresh_induct = Morphism.thm phi fresh_induct
} : least_fp_thms;

type greatest_fp_thms = {
  existential_coinduct: thm,
  fresh_coinduct_param: thm
};

fun morph_greatest_fp_thms phi { existential_coinduct, fresh_coinduct_param } = {
  existential_coinduct = Morphism.thm phi existential_coinduct,
  fresh_coinduct_param = Morphism.thm phi fresh_coinduct_param
}: greatest_fp_thms;

type fp_result = {
  fp: BNF_Util.fp_kind,
  binding_relation: int list list list,
  rec_vars: int list,
  bfree_vars: int list,
  raw_fps: raw_result fp_result_T list,
  quotient_fps: quotient_result fp_result_T list,
  fp_thms: (least_fp_thms, greatest_fp_thms) MRBNF_Util.either option,
  pre_mrbnfs: MRBNF_Def.mrbnf list
};

fun morph_fp_result phi ({ fp, binding_relation, rec_vars, bfree_vars, raw_fps, quotient_fps, fp_thms, pre_mrbnfs }) = {
  fp = fp, binding_relation = binding_relation, rec_vars = rec_vars, bfree_vars = bfree_vars,
  raw_fps = map (morph_fp_result_T morph_raw_result phi) raw_fps,
  quotient_fps = map (morph_fp_result_T morph_quotient_result phi) quotient_fps,
  fp_thms = Option.map (MRBNF_Util.map_sum (morph_least_fp_thms phi) (morph_greatest_fp_thms phi)) fp_thms,
  pre_mrbnfs = map (MRBNF_Def.morph_mrbnf phi) pre_mrbnfs
} : fp_result;

fun substitute_vars replacements fp_result =
  let
    val phi = Morphism.morphism "instantiate vars" {
      binding = [], fact = [],
      typ = [fn _ => Term.typ_subst_atomic replacements],
      term = [fn _ => Term.subst_atomic_types replacements]
    };
  in morph_fp_result phi fp_result end;

structure Data = Generic_Data (
  type T = fp_result Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
);

val register_fp_results = fold (fn fp_result as { quotient_fps, ...} => fold (fn { T = Type (s, _), ...} =>
  Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
    (fn phi => Data.map (Symtab.update (s, morph_fp_result phi fp_result)))) quotient_fps);

fun fp_result_of_generic context =
  Option.map (morph_fp_result (Morphism.transfer_morphism (Context.theory_of context)))
  o Symtab.lookup (Data.get context);

val fp_result_of = fp_result_of_generic o Context.Proof;

fun note_fp_result (fp_res : fp_result) lthy =
  let
    fun note_internals (quot : quotient_result fp_result_T) = [
      ("permute_ctor", [#permute_ctor quot]),
      ("permute_abs", [#permute_abs (#inner quot)]),
      ("FVars_ctor", #FVars_ctors quot),
      ("FVars_intros", flat (#FVars_intross quot)),
      ("FVars_bd", #card_of_FVars_bounds quot),
      ("FVars_bd_UNIVs", #card_of_FVars_bound_UNIVs quot),
      ("nnoclash_noclash", [#nnoclash_noclash (#inner quot)]),
      ("total_abs_eq_iff", [#total_abs_eq_iff (#inner quot)]),
      ("TT_fresh_cases", [#fresh_cases (#inner quot)]),
      ("abs_rep", [#abs_rep (#inner quot)]),
      ("rep_abs", [#rep_abs (#inner quot)]),
      ("rep_abs_sym", [#rep_abs_sym (#inner quot)]),
      ("abs_ctor", [#abs_ctor (#inner quot)]),
      ("TT_inject0", [#inject quot])
    ];

    fun note_always (quot : quotient_result fp_result_T) = [
      ("noclash_permute", [#noclash_permute (#inner quot)]),
      ("permute_id0", [#permute_id0 quot]),
      ("permute_id", [#permute_id quot]),
      ("permute_comp0", [#permute_comp0 quot]),
      ("permute_comp", [#permute_comp quot]),
      ("FVars_permute", #FVars_permutes quot),
      ("permute_cong", [#permute_cong (#inner quot)]),
      ("permute_cong_id", [#permute_cong_id (#inner quot)]),
      ("permute_bij", [#permute_bij (#inner quot)]),
      ("permute_inv_simp", [#permute_inv_simp (#inner quot)])
    ];

    fun note_quot (quot : quotient_result fp_result_T) =
      (if Config.get lthy MRBNF_Def.mrbnf_internals then
        note_internals quot
        @ the_default [] (Option.map (MRBNF_Util.either (fn fp_thms => [
          ("wf_subshape", [#wf_subshape fp_thms]),
          ("set_subshapes", flat (#set_subshapess fp_thms)),
          ("set_subshape_permutes", flat (#set_subshape_permutess fp_thms)),
          ("subshape_induct", [#subshape_induct fp_thms]),
          ("existential_induct", [#existential_induct fp_thms]),
          ("fresh_induct_param", [#fresh_induct_param fp_thms]),
          ("TT_fresh_induct", [#fresh_induct fp_thms])
        ]) (fn gfp_thms => [
          ("existential_coinduct", [#existential_coinduct gfp_thms]),
          ("fresh_coinduct_param", [#fresh_coinduct_param gfp_thms])
        ])) (#fp_thms fp_res))
      else [])
      @ note_always quot;

    fun note_raw (raw : raw_result fp_result_T) =
      (if Config.get lthy MRBNF_Def.mrbnf_internals then [
        ("alpha_FVars", #alpha_FVarss (#inner raw)),
        ("alpha_trans", [#alpha_trans (#inner raw)]),
        ("permute_raw_ctor", [#permute_ctor raw]),
        ("permute_raw_comp0s", [#permute_comp0 raw]),
        ("permute_raw_comps", [#permute_comp raw]),
        ("alpha_bij_eq", [#alpha_bij_eq (#inner raw)]),
        ("alpha_refl", [#alpha_refl (#inner raw)]),
        ("FVars_raw_permute", #FVars_permutes raw),
        ("permute_raw_id", [#permute_id raw])
      ] else []);

    val notes = flat (map2 (fn quot => fn raw => map (fn (thmN, thms) =>
      ((Binding.qualify true (MRBNF_Util.short_type_name (fst (dest_Type (#T quot)))) (Binding.name thmN), []),
        [(thms, [])]
      )
    ) (note_quot quot @ note_raw raw)) (#quotient_fps fp_res) (#raw_fps fp_res));

    val (_, lthy) = Local_Theory.notes notes lthy;
  in lthy end;

end;