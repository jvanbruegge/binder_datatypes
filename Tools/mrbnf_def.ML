signature MRBNF_DEF =
sig
  type mrbnf
  type nonemptiness_witness = {I: int list, wit: term, prop: thm list}
  type mrbnf_def_tactics = {
    map_id0: Proof.context -> tactic,
    map_comp0: Proof.context -> tactic,
    map_cong0: Proof.context -> tactic,
    set_map0: (Proof.context -> tactic) list,
    infinite_regular_card_order: Proof.context -> tactic,
    set_bd: (Proof.context -> tactic) list,
    le_rel_OO: Proof.context -> tactic,
    in_rel: Proof.context -> tactic,
    pred_set: Proof.context -> tactic,
    wit: Proof.context -> tactic
  }
  type class_thms = {
    var_large: thm,
    var_regular: thm,
    covar_large: thm
  }

  val morph_mrbnf: morphism -> mrbnf -> mrbnf
  val morph_mrbnf_defs: morphism -> mrbnf -> mrbnf
  val permute_deads: (typ list -> typ list) -> mrbnf -> mrbnf
  val transfer_mrbnf: theory -> mrbnf -> mrbnf
  val mrbnf_of: Proof.context -> string -> mrbnf option
  val mrbnf_of_global: theory -> string -> mrbnf option
  val mrbnf_of_bnf: BNF_Def.bnf -> local_theory -> (mrbnf * local_theory)
  val bnf_of_mrbnf: mrbnf -> local_theory -> (BNF_Def.bnf option * local_theory)
  val as_mrbnf: string -> local_theory -> (mrbnf * local_theory) option
  val mrbnf_interpretation: string -> (mrbnf -> local_theory -> local_theory) -> theory -> theory
  val interpret_mrbnf: (string -> bool) -> mrbnf -> local_theory -> local_theory
  val register_mrbnf_raw: string -> mrbnf -> local_theory -> local_theory
  val register_mrbnf: (string -> bool) -> string -> mrbnf -> local_theory -> local_theory
  val register_bnf_as_mrbnf: string option -> BNF_Def.bnf -> local_theory -> (mrbnf * local_theory)
  val register_mrbnf_as_bnf: mrbnf -> local_theory -> (BNF_Def.bnf option * local_theory)

  datatype var_type = Live_Var | Bound_Var | Free_Var | Dead_Var; (*Added Dead_Var for kill function*)
  val var_type_ord: var_type ord

  val interlace: 'a list -> 'a list -> 'a list -> var_type list -> 'a list
  val deinterlace: 'a list -> var_type list -> 'a list * 'a list * 'a list

  val name_of_mrbnf: mrbnf -> binding
  val T_of_mrbnf: mrbnf -> typ
  val var_types_of_mrbnf: mrbnf -> var_type list
  val free_of_mrbnf: mrbnf -> int
  val frees_of_mrbnf: mrbnf -> typ list
  val bound_of_mrbnf: mrbnf -> int
  val bounds_of_mrbnf: mrbnf -> typ list
  val live_of_mrbnf: mrbnf -> int
  val lives_of_mrbnf: mrbnf -> typ list
  val lives'_of_mrbnf: mrbnf -> typ list
  val dead_of_mrbnf: mrbnf -> int
  val deads_of_mrbnf: mrbnf -> typ list
  val bd_of_mrbnf: mrbnf -> term
  val class_of_mrbnf: mrbnf -> sort
  val coclass_of_mrbnf: mrbnf -> sort
  val nwits_of_mrbnf: mrbnf -> int

  val mapN: string
  val predN: string
  val relN: string
  val mr_relN: string
  val setN: string
  val mk_setN: int -> string
  val mk_witN: int -> string

  val map_of_mrbnf: mrbnf -> term
  val pred_of_mrbnf: mrbnf -> term
  val rel_of_mrbnf: mrbnf -> term
  val mr_rel_of_mrbnf: mrbnf -> term
  val sets_of_mrbnf: mrbnf -> term list

  val mk_T_of_mrbnf: typ list -> typ list -> typ list -> typ list -> mrbnf -> typ
  val mk_bd_of_mrbnf: typ list -> typ list -> typ list -> mrbnf -> term
  val mk_map_of_mrbnf: typ list -> typ list ->  typ list -> typ list -> typ list -> mrbnf -> term
  val mk_pred_of_mrbnf: typ list -> typ list -> typ list -> typ list -> mrbnf -> term
  val mk_rel_of_mrbnf: typ list -> typ list -> typ list -> typ list -> typ list -> mrbnf -> term
  val mk_mr_rel_of_mrbnf: typ list -> typ list -> typ list -> typ list -> typ list -> mrbnf -> term
  val mk_sets_of_mrbnf: typ list list -> typ list list -> typ list list -> typ list list -> mrbnf ->
    term list
  val mk_wits_of_mrbnf: typ list list -> typ list list -> typ list list -> typ list list -> mrbnf ->
    (int list * term) list

  val mk_map_comb_of_mrbnf: typ list -> term list -> term list -> term list -> mrbnf -> term

  val bd_infinite_regular_card_order_of_mrbnf: mrbnf -> thm
  val bd_Card_order_of_mrbnf: mrbnf -> thm
  val bd_Cinfinite_of_mrbnf: mrbnf -> thm
  val bd_Cnotzero_of_mrbnf: mrbnf -> thm
  val bd_card_order_of_mrbnf: mrbnf -> thm
  val bd_cinfinite_of_mrbnf: mrbnf -> thm
  val bd_regularCard_of_mrbnf: mrbnf -> thm
  val collect_set_map_of_mrbnf: mrbnf -> thm
  val in_bd_of_mrbnf: mrbnf -> thm
  val in_cong_of_mrbnf: mrbnf -> thm
  val in_mono_of_mrbnf: mrbnf -> thm
  val in_rel_of_mrbnf: mrbnf -> thm
  val inj_map_of_mrbnf: mrbnf -> thm
  val inj_map_strong_of_mrbnf: mrbnf -> thm
  val le_rel_OO_of_mrbnf: mrbnf -> thm
  val map_comp0_of_mrbnf: mrbnf -> thm
  val map_comp_of_mrbnf: mrbnf -> thm
  val map_cong0_of_mrbnf: mrbnf -> thm
  val map_cong_of_mrbnf: mrbnf -> thm
  val map_cong_pred_of_mrbnf: mrbnf -> thm
  val map_cong_simp_of_mrbnf: mrbnf -> thm
  val map_def_of_mrbnf: mrbnf -> thm
  val map_id0_of_mrbnf: mrbnf -> thm
  val map_id_of_mrbnf: mrbnf -> thm
  val map_ident0_of_mrbnf: mrbnf -> thm
  val map_ident_of_mrbnf: mrbnf -> thm
  val map_transfer_of_mrbnf: mrbnf -> thm
  val pred_cong0_of_mrbnf: mrbnf -> thm
  val pred_cong_of_mrbnf: mrbnf -> thm
  val pred_cong_simp_of_mrbnf: mrbnf -> thm
  val pred_def_of_mrbnf: mrbnf -> thm
  val pred_map_of_mrbnf: mrbnf -> thm
  val pred_mono_strong0_of_mrbnf: mrbnf -> thm
  val pred_mono_strong_of_mrbnf: mrbnf -> thm
  val pred_mono_of_mrbnf: mrbnf -> thm
  val pred_set_of_mrbnf: mrbnf -> thm
  val pred_rel_of_mrbnf: mrbnf -> thm
  val pred_transfer_of_mrbnf: mrbnf -> thm
  val pred_True_of_mrbnf: mrbnf -> thm
  val rel_Grp_of_mrbnf: mrbnf -> thm
  val rel_OO_Grp_of_mrbnf: mrbnf -> thm
  val rel_OO_Grp_id_of_mrbnf: mrbnf -> thm
  val rel_OO_of_mrbnf: mrbnf -> thm
  val rel_cong0_of_mrbnf: mrbnf -> thm
  val rel_cong_of_mrbnf: mrbnf -> thm
  val rel_cong_simp_of_mrbnf: mrbnf -> thm
  val rel_conversep_of_mrbnf: mrbnf -> thm
  val rel_def_of_mrbnf: mrbnf -> thm
  val rel_eq_of_mrbnf: mrbnf -> thm
  val rel_flip_of_mrbnf: mrbnf -> thm
  val rel_map_of_mrbnf: mrbnf -> thm list
  val rel_mono_of_mrbnf: mrbnf -> thm
  val rel_mono_strong0_of_mrbnf: mrbnf -> thm
  val rel_mono_strong_of_mrbnf: mrbnf -> thm
  val rel_eq_onp_of_mrbnf: mrbnf -> thm
  val rel_refl_of_mrbnf: mrbnf -> thm
  val rel_refl_strong_of_mrbnf: mrbnf -> thm
  val rel_reflp_of_mrbnf: mrbnf -> thm
  val rel_symp_of_mrbnf: mrbnf -> thm
  val rel_transfer_of_mrbnf: mrbnf -> thm
  val rel_transp_of_mrbnf: mrbnf -> thm
  val set_bd_of_mrbnf: mrbnf -> thm list
  val set_bd_UNIV_of_mrbnf: mrbnf -> thm list
  val set_defs_of_mrbnf: mrbnf -> thm list
  val set_map0_of_mrbnf: mrbnf -> thm list
  val set_map_of_mrbnf: mrbnf -> thm list
  val set_transfer_of_mrbnf: mrbnf -> thm list
  val wit_thms_of_mrbnf: mrbnf -> thm list
  val wit_thmss_of_mrbnf: mrbnf -> thm list list

  val class_thms_of_mrbnf: mrbnf -> class_thms

  val var_large_of_mrbnf: mrbnf -> thm
  val var_regular_of_mrbnf: mrbnf -> thm
  val natLeq_bound_of_mrbnf: mrbnf -> thm
  val UNIV_cinfinite_of_mrbnf: mrbnf -> thm
  val supp_comp_bound_of_mrbnf: mrbnf -> thm
  val Un_bound_of_mrbnf: mrbnf -> thm
  val UNION_bound_of_mrbnf: mrbnf -> thm
  val mr_rel_cong_of_mrbnf: mrbnf -> thm
  val mr_rel_cong0_of_mrbnf: mrbnf -> thm
  val mr_in_rel_of_mrbnf: mrbnf -> thm
  val mr_le_rel_OO_of_mrbnf: mrbnf -> thm
  val mr_map_transfer_of_mrbnf: mrbnf -> thm
  val mr_rel_Grp_of_mrbnf: mrbnf -> thm
  val mr_rel_OO_Grp_of_mrbnf: mrbnf -> thm
  val mr_rel_OO_of_mrbnf: mrbnf -> thm
  val mr_rel_conversep_of_mrbnf: mrbnf -> thm
  val mr_rel_def_of_mrbnf: mrbnf -> thm
  val mr_rel_eq_of_mrbnf: mrbnf -> thm
  val mr_rel_flip_of_mrbnf: mrbnf -> thm
  val mr_rel_map_of_mrbnf: mrbnf -> thm list
  val mr_rel_mono_of_mrbnf: mrbnf -> thm
  val mr_rel_mono_strong0_of_mrbnf: mrbnf -> thm
  val mr_rel_mono_strong_of_mrbnf: mrbnf -> thm
  val mr_rel_transfer_of_mrbnf: mrbnf -> thm
  val mr_set_transfer_of_mrbnf: mrbnf -> thm list
  val mr_rel_id_of_mrbnf: mrbnf -> thm
  val mr_rel_set_of_mrbnf: mrbnf -> thm list

  val mk_map: int -> int -> int -> typ list -> typ list -> term -> term
  val mk_pred: typ list -> term -> term
  val mk_rel: int -> int -> int -> typ list -> typ list -> term -> term
  val mk_mr_rel: int -> int -> int -> typ list -> typ list -> term -> term
  val mk_set: typ list -> term -> term
  val build_map: Proof.context -> typ list -> typ list -> (typ * typ -> term) -> typ * typ -> term
  val build_rel: (string * (int * int * int * term)) list -> Proof.context -> typ list ->
    typ list -> (typ * typ -> term) -> typ * typ -> term
  val build_mr_rel: (string * (int * int * int * term)) list -> Proof.context -> typ list ->
    typ list -> (typ * typ -> term) -> typ * typ -> term
  val build_set: Proof.context -> typ -> typ -> term
  val flatten_type_args_of_mrbnf: mrbnf -> 'a -> 'a list -> 'a list -> 'a list -> 'a list
  val map_flattened_map_args: Proof.context -> string -> (term list -> 'a list) -> term list ->
    term list -> term list -> 'a list

  val mk_witness: int list * term -> thm list -> nonemptiness_witness
  val mk_wit_goals: term list -> term list -> term list -> int list * term -> term list
  val minimize_wits: (''a list * 'b) list -> (''a list * 'b) list
  val wits_of_mrbnf: mrbnf -> nonemptiness_witness list

  val zip_axioms: 'a -> 'a -> 'a -> 'a list -> 'a -> 'a list -> 'a -> 'a -> 'a -> 'a list

  datatype inline_policy = Dont_Inline | Hardly_Inline | Smart_Inline | Do_Inline
  datatype fact_policy = Dont_Note | Note_Some | Note_All

  val mrbnf_internals: bool Config.T
  val mrbnf_verbose: bool Config.T
  val mrbnf_timing: bool Config.T
  val user_policy: fact_policy -> Proof.context -> fact_policy
  val note_mrbnf_thms: fact_policy -> (binding -> binding) -> binding -> mrbnf -> local_theory ->
    mrbnf * local_theory
  val note_mrbnf_defs: mrbnf -> local_theory -> mrbnf * local_theory

 (*val mk_lab_sets_of_mrbnf: typ list list -> typ list list -> typ list list -> typ list list -> mrbnf ->
    (var_type *term) list
 *)

  val print_mrbnfs: Proof.context -> unit
  val prepare_def: inline_policy -> (Proof.context -> fact_policy) -> bool ->
    (binding -> binding) -> (Proof.context -> 'a -> typ) -> (Proof.context -> 'b -> term) -> (Proof.context -> 'c -> sort) ->
    typ list option -> ((sort * thm * thm) * (sort * (sort * local_theory -> thm))) option -> binding -> binding -> binding -> binding list ->
    (((((((binding * 'a) * 'b) * (var_type * 'b) list) * 'b) * 'b list) * 'b option) * 'b option) * 'c option ->
    Proof.context ->
    string * term list * ((Proof.context -> thm list -> tactic) option * term list list) *
    ((thm list -> thm list list) -> thm list list -> Proof.context -> mrbnf * local_theory) *
    local_theory * thm list
  val define_mrbnf_consts: inline_policy -> fact_policy -> bool -> typ list option ->
    ((sort * thm * thm) * (sort * (sort * local_theory -> thm))) option -> binding -> binding -> binding -> binding list ->
    (((((((binding * typ) * term) * (var_type * term) list) * term) * term list) * term option)
    * term option) * sort option -> local_theory ->
      ((typ list * typ list * typ list * typ *
        (string list * thm * thm) *
         ((thm -> local_theory -> string list * local_theory) * (string list * local_theory -> thm))) *
       (term * term list * term * (int list * term) list * term * term) *
       (thm * thm list * thm * thm list * thm * thm) *
       ((typ list -> typ list -> typ list -> term) *
        (typ list -> typ list -> term -> term) *
        (typ list -> typ list -> typ -> typ) *
        (typ list -> (typ list * typ list) -> (typ list * typ list) -> term) *
        (typ list -> (typ list * typ list) -> term) *
        (typ list -> term list -> term) *
        (typ list -> typ list -> term))) * local_theory

  val get_class_assumption: sort -> string -> local_theory -> thm

  val mrbnf_def: inline_policy -> (Proof.context -> fact_policy) -> bool -> (binding -> binding) ->
    mrbnf_def_tactics -> typ list option ->
    ((sort * thm * thm) * (sort * (sort * local_theory -> thm))) option -> binding -> binding -> binding -> binding list ->
    ((((((binding * typ) * term) * (var_type * term) list) * term) * term list) * term option) * term option ->
    local_theory -> mrbnf * local_theory
  val mrbnf_cmd: ((((((((binding * string) * string) * (var_type * string) list) * string)
      * string list) * string option) * string option) * string option) * (Proof.context -> Plugin_Name.filter) ->
    Proof.context -> Proof.state
end;

structure MRBNF_Def : MRBNF_DEF =
struct

open MRBNF_Util
open BNF_Tactics
open MRBNF_Def_Tactics

val undefT = TFree (Name.aT, @{sort type});

fun short_type_name full_name = String.tokens (fn c => c = #".") full_name |> List.last;

fun list_of_pair (x, y) = [x, y];
fun count P = length o filter P;

val fst_binder_type = fastype_of #> binder_types #> hd;
fun add_dummy t = t $ (fst_binder_type t |> Term.dummy_pattern);

fun mk_regularCard t = Const (@{const_name regularCard}, fastype_of t --> HOLogic.boolT) $ t;

val fundefcong_attrs = @{attributes [fundef_cong]};
val mono_attrs = @{attributes [mono]};

type axioms = {
  map_id0: thm,
  map_comp0: thm,
  map_cong0: thm,
  set_map0: thm list,
  bd_infinite_regular_card_order: thm,
  set_bd: thm list,
  le_rel_OO: thm,
  rel_OO_Grp: thm,
  pred_set: thm
};

fun mk_axioms' ((((((((id, comp), cong), map), bd), set_bd), le_rel_OO), rel), pred) =
  {map_id0 = id, map_comp0 = comp, map_cong0 = cong, set_map0 = map, bd_infinite_regular_card_order = bd,
   set_bd = set_bd, le_rel_OO = le_rel_OO, rel_OO_Grp = rel, pred_set = pred};

fun dest_cons [] = raise List.Empty
  | dest_cons (x :: xs) = (x, xs);

fun mk_axioms n thms = thms
  |> map the_single
  |> dest_cons
  ||>> dest_cons
  ||>> dest_cons
  ||>> chop n
  ||>> dest_cons
  ||>> chop n
  ||>> dest_cons
  ||>> dest_cons
  ||> the_single
  |> mk_axioms';

fun zip_axioms mid mcomp mcong smap bd sbd le_rel_OO rel pred =
  [mid, mcomp, mcong] @ smap @ [bd] @ sbd @ [le_rel_OO, rel, pred];

fun map_axioms f {map_id0, map_comp0, map_cong0, set_map0, bd_infinite_regular_card_order, set_bd,
  le_rel_OO, rel_OO_Grp, pred_set} =
  {map_id0 = f map_id0,
    map_comp0 = f map_comp0,
    map_cong0 = f map_cong0,
    set_map0 = map f set_map0,
    bd_infinite_regular_card_order = f bd_infinite_regular_card_order,
    set_bd = map f set_bd,
    le_rel_OO = f le_rel_OO,
    rel_OO_Grp = f rel_OO_Grp,
    pred_set = f pred_set};

val morph_axioms = map_axioms o Morphism.thm;

type class_thms = {
  var_large: thm,
  var_regular: thm,
  covar_large: thm
}

type defs = {
  map_def: thm,
  set_defs: thm list,
  rel_def: thm,
  mr_rel_def: thm,
  pred_def: thm
}

fun mk_defs map sets rel mr_rel pred = {map_def = map, set_defs = sets, rel_def = rel,
  mr_rel_def = mr_rel, pred_def = pred};

fun map_defs f {map_def, set_defs, rel_def, mr_rel_def, pred_def} =
  {map_def = f map_def, set_defs = map f set_defs, rel_def = f rel_def, mr_rel_def = f mr_rel_def,
    pred_def = f pred_def};

val morph_defs = map_defs o Morphism.thm;

type facts = {
  bd_card_order: thm,
  bd_cinfinite: thm,
  bd_regularCard: thm,
  bd_Card_order: thm,
  bd_Cinfinite: thm,
  bd_Cnotzero: thm,
  collect_set_map: thm lazy,
  in_bd: thm lazy,
  in_cong: thm lazy,
  in_mono: thm lazy,
  in_rel: thm lazy,
  inj_map: thm lazy,
  inj_map_strong: thm lazy,
  map_comp: thm lazy,
  map_cong: thm lazy,
  map_cong_simp: thm lazy,
  map_cong_pred: thm lazy,
  map_id: thm lazy,
  map_ident0: thm lazy,
  map_ident: thm lazy,
  map_transfer: thm lazy,
  rel_eq: thm lazy,
  rel_flip: thm lazy,
  set_map: thm lazy list,
  set_bd_UNIV: thm lazy list,
  rel_cong0: thm lazy,
  rel_cong: thm lazy,
  rel_cong_simp: thm lazy,
  rel_map: thm list lazy,
  rel_mono: thm lazy,
  rel_mono_strong0: thm lazy,
  rel_mono_strong: thm lazy,
  set_transfer: thm list lazy,
  rel_Grp: thm lazy,
  rel_conversep: thm lazy,
  rel_OO: thm lazy,
  rel_OO_Grp_id: thm lazy,
  rel_refl: thm lazy,
  rel_refl_strong: thm lazy,
  rel_reflp: thm lazy,
  rel_symp: thm lazy,
  rel_transp: thm lazy,
  rel_transfer: thm lazy,
  rel_eq_onp: thm lazy,
  pred_transfer: thm lazy,
  pred_True: thm lazy,
  pred_map: thm lazy,
  pred_rel: thm lazy,
  pred_mono_strong0: thm lazy,
  pred_mono_strong: thm lazy,
  pred_mono: thm lazy,
  pred_cong0: thm lazy,
  pred_cong: thm lazy,
  pred_cong_simp: thm lazy
};

fun mk_facts bd_card_order bd_cinfinite bd_regularCard bd_Card_order bd_Cinfinite bd_Cnotzero
    collect_set_map in_bd in_cong in_mono in_rel inj_map inj_map_strong map_comp map_cong
    map_cong_simp map_cong_pred map_id map_ident0 map_ident map_transfer
    rel_eq rel_flip set_map set_bd_UNIV rel_cong0 rel_cong rel_cong_simp rel_map rel_mono rel_mono_strong0
    rel_mono_strong set_transfer rel_Grp rel_conversep rel_OO rel_OO_Grp_id rel_refl
    rel_refl_strong rel_reflp rel_symp rel_transp rel_transfer rel_eq_onp pred_transfer pred_True
    pred_map pred_rel pred_mono_strong0 pred_mono_strong pred_mono pred_cong0 pred_cong
    pred_cong_simp = {
  bd_card_order = bd_card_order,
  bd_cinfinite = bd_cinfinite,
  bd_regularCard = bd_regularCard,
  bd_Card_order = bd_Card_order,
  bd_Cinfinite = bd_Cinfinite,
  bd_Cnotzero = bd_Cnotzero,
  collect_set_map = collect_set_map,
  in_bd = in_bd,
  in_cong = in_cong,
  in_mono = in_mono,
  in_rel = in_rel,
  inj_map = inj_map,
  inj_map_strong = inj_map_strong,
  map_comp = map_comp,
  map_cong = map_cong,
  map_cong_simp = map_cong_simp,
  map_cong_pred = map_cong_pred,
  map_id = map_id,
  map_ident0 = map_ident0,
  map_ident = map_ident,
  map_transfer = map_transfer,
  rel_eq = rel_eq,
  rel_flip = rel_flip,
  set_map = set_map,
  set_bd_UNIV = set_bd_UNIV,
  rel_cong0 = rel_cong0,
  rel_cong = rel_cong,
  rel_cong_simp = rel_cong_simp,
  rel_map = rel_map,
  rel_mono = rel_mono,
  rel_mono_strong0 = rel_mono_strong0,
  rel_mono_strong = rel_mono_strong,
  rel_transfer = rel_transfer,
  rel_Grp = rel_Grp,
  rel_conversep = rel_conversep,
  rel_OO = rel_OO,
  rel_OO_Grp_id = rel_OO_Grp_id,
  rel_refl = rel_refl,
  rel_refl_strong = rel_refl_strong,
  rel_reflp = rel_reflp,
  rel_symp = rel_symp,
  rel_transp = rel_transp,
  set_transfer = set_transfer,
  rel_eq_onp = rel_eq_onp,
  pred_transfer = pred_transfer,
  pred_True = pred_True,
  pred_map = pred_map,
  pred_rel = pred_rel,
  pred_mono_strong0 = pred_mono_strong0,
  pred_mono_strong = pred_mono_strong,
  pred_mono = pred_mono,
  pred_cong0 = pred_cong0,
  pred_cong = pred_cong,
  pred_cong_simp = pred_cong_simp};

fun map_facts f {
  bd_card_order,
  bd_cinfinite,
  bd_regularCard,
  bd_Card_order,
  bd_Cinfinite,
  bd_Cnotzero,
  collect_set_map,
  in_bd,
  in_cong,
  in_mono,
  in_rel,
  inj_map,
  inj_map_strong,
  map_comp,
  map_cong,
  map_cong_simp,
  map_cong_pred,
  map_id,
  map_ident0,
  map_ident,
  map_transfer,
  rel_eq,
  rel_flip,
  set_map,
  set_bd_UNIV,
  rel_cong0,
  rel_cong,
  rel_cong_simp,
  rel_map,
  rel_mono,
  rel_mono_strong0,
  rel_mono_strong,
  rel_transfer,
  rel_Grp,
  rel_conversep,
  rel_OO,
  rel_OO_Grp_id,
  rel_refl,
  rel_refl_strong,
  rel_reflp,
  rel_symp,
  rel_transp,
  set_transfer,
  rel_eq_onp,
  pred_transfer,
  pred_True,
  pred_map,
  pred_rel,
  pred_mono_strong0,
  pred_mono_strong,
  pred_mono,
  pred_cong0,
  pred_cong,
  pred_cong_simp} =
  {bd_card_order = f bd_card_order,
    bd_cinfinite = f bd_cinfinite,
    bd_regularCard = f bd_regularCard,
    bd_Card_order = f bd_Card_order,
    bd_Cinfinite = f bd_Cinfinite,
    bd_Cnotzero = f bd_Cnotzero,
    collect_set_map = Lazy.map f collect_set_map,
    in_bd = Lazy.map f in_bd,
    in_cong = Lazy.map f in_cong,
    in_mono = Lazy.map f in_mono,
    in_rel = Lazy.map f in_rel,
    inj_map = Lazy.map f inj_map,
    inj_map_strong = Lazy.map f inj_map_strong,
    map_comp = Lazy.map f map_comp,
    map_cong = Lazy.map f map_cong,
    map_cong_simp = Lazy.map f map_cong_simp,
    map_cong_pred = Lazy.map f map_cong_pred,
    map_id = Lazy.map f map_id,
    map_ident0 = Lazy.map f map_ident0,
    map_ident = Lazy.map f map_ident,
    map_transfer = Lazy.map f map_transfer,
    rel_eq = Lazy.map f rel_eq,
    rel_flip = Lazy.map f rel_flip,
    set_map = map (Lazy.map f) set_map,
    set_bd_UNIV = map (Lazy.map f) set_bd_UNIV,
    rel_cong0 = Lazy.map f rel_cong0,
    rel_cong = Lazy.map f rel_cong,
    rel_cong_simp = Lazy.map f rel_cong_simp,
    rel_map = Lazy.map (map f) rel_map,
    rel_mono = Lazy.map f rel_mono,
    rel_mono_strong0 = Lazy.map f rel_mono_strong0,
    rel_mono_strong = Lazy.map f rel_mono_strong,
    rel_transfer = Lazy.map f rel_transfer,
    rel_Grp = Lazy.map f rel_Grp,
    rel_conversep = Lazy.map f rel_conversep,
    rel_OO = Lazy.map f rel_OO,
    rel_OO_Grp_id = Lazy.map f rel_OO_Grp_id,
    rel_refl = Lazy.map f rel_refl,
    rel_refl_strong = Lazy.map f rel_refl_strong,
    rel_reflp = Lazy.map f rel_reflp,
    rel_symp = Lazy.map f rel_symp,
    rel_transp = Lazy.map f rel_transp,
    set_transfer = Lazy.map (map f) set_transfer,
    rel_eq_onp = Lazy.map f rel_eq_onp,
    pred_transfer = Lazy.map f pred_transfer,
    pred_True = Lazy.map f pred_True,
    pred_map = Lazy.map f pred_map,
    pred_rel = Lazy.map f pred_rel,
    pred_mono_strong0 = Lazy.map f pred_mono_strong0,
    pred_mono_strong = Lazy.map f pred_mono_strong,
    pred_mono = Lazy.map f pred_mono,
    pred_cong0 = Lazy.map f pred_cong0,
    pred_cong = Lazy.map f pred_cong,
    pred_cong_simp = Lazy.map f pred_cong_simp};

val morph_facts = map_facts o Morphism.thm;

type mr_facts = {
  var_large: thm,
  var_regular: thm,
  natLeq_bound: thm,
  UNIV_cinfinite: thm,
  supp_comp_bound: thm,
  Un_bound: thm,
  UNION_bound: thm,
  mr_rel_cong0: thm lazy,
  mr_rel_cong: thm lazy,
  mr_in_rel: thm lazy,
  mr_le_rel_OO: thm lazy,
  mr_map_transfer: thm lazy,
  mr_rel_eq: thm lazy,
  mr_rel_flip: thm lazy,
  mr_rel_map: thm list lazy,
  mr_rel_mono: thm lazy,
  mr_rel_mono_strong0: thm lazy,
  mr_rel_mono_strong: thm lazy,
  mr_set_transfer: thm list lazy,
  mr_rel_Grp: thm lazy,
  mr_rel_conversep: thm lazy,
  mr_rel_OO: thm lazy,
  mr_rel_OO_Grp: thm lazy,
  mr_rel_transfer: thm lazy,
  mr_rel_id: thm lazy,
  mr_rel_set: thm list lazy
};

fun mk_mr_facts var_large var_regular natLeq_bound UNIV_cinfinite supp_comp_bound Un_bound
    UNION_bound mr_rel_cong0 mr_rel_cong mr_in_rel mr_le_rel_OO mr_map_transfer mr_rel_eq mr_rel_flip mr_rel_map mr_rel_mono
    mr_rel_mono_strong0 mr_rel_mono_strong mr_set_transfer mr_rel_Grp mr_rel_conversep mr_rel_OO
    mr_rel_OO_Grp mr_rel_transfer mr_rel_id mr_rel_set = {
  var_large = var_large,
  var_regular = var_regular,
  natLeq_bound = natLeq_bound,
  UNIV_cinfinite = UNIV_cinfinite,
  supp_comp_bound = supp_comp_bound,
  Un_bound = Un_bound,
  UNION_bound = UNION_bound,
  mr_rel_cong0 = mr_rel_cong0,
  mr_rel_cong = mr_rel_cong,
  mr_in_rel = mr_in_rel,
  mr_le_rel_OO = mr_le_rel_OO,
  mr_map_transfer = mr_map_transfer,
  mr_rel_eq = mr_rel_eq,
  mr_rel_flip = mr_rel_flip,
  mr_rel_map = mr_rel_map,
  mr_rel_mono = mr_rel_mono,
  mr_rel_mono_strong0 = mr_rel_mono_strong0,
  mr_rel_mono_strong = mr_rel_mono_strong,
  mr_set_transfer = mr_set_transfer,
  mr_rel_Grp = mr_rel_Grp,
  mr_rel_conversep = mr_rel_conversep,
  mr_rel_OO = mr_rel_OO,
  mr_rel_OO_Grp = mr_rel_OO_Grp,
  mr_rel_transfer = mr_rel_transfer,
  mr_rel_id = mr_rel_id,
  mr_rel_set = mr_rel_set};

fun map_mr_facts f {
  var_large,
  var_regular,
  natLeq_bound,
  UNIV_cinfinite,
  supp_comp_bound,
  Un_bound,
  UNION_bound,
  mr_rel_cong0,
  mr_rel_cong,
  mr_in_rel,
  mr_le_rel_OO,
  mr_map_transfer,
  mr_rel_eq,
  mr_rel_flip,
  mr_rel_map,
  mr_rel_mono,
  mr_rel_mono_strong0,
  mr_rel_mono_strong,
  mr_set_transfer,
  mr_rel_Grp,
  mr_rel_conversep,
  mr_rel_OO,
  mr_rel_OO_Grp,
  mr_rel_transfer,
  mr_rel_id,
  mr_rel_set} =
  {var_large = f var_large,
  var_regular = f var_regular,
  natLeq_bound = f natLeq_bound,
  UNIV_cinfinite = f UNIV_cinfinite,
  supp_comp_bound = f supp_comp_bound,
  Un_bound = f Un_bound,
  UNION_bound = f UNION_bound,
  mr_rel_cong0 = Lazy.map f mr_rel_cong0,
  mr_rel_cong = Lazy.map f mr_rel_cong,
  mr_in_rel = Lazy.map f mr_in_rel,
  mr_le_rel_OO = Lazy.map f mr_le_rel_OO,
  mr_map_transfer = Lazy.map f mr_map_transfer,
  mr_rel_eq = Lazy.map f mr_rel_eq,
  mr_rel_flip = Lazy.map f mr_rel_flip,
  mr_rel_map = Lazy.map (map f) mr_rel_map,
  mr_rel_mono = Lazy.map f mr_rel_mono,
  mr_rel_mono_strong0 = Lazy.map f mr_rel_mono_strong0,
  mr_rel_mono_strong = Lazy.map f mr_rel_mono_strong,
  mr_set_transfer = Lazy.map (map f) mr_set_transfer,
  mr_rel_Grp = Lazy.map f mr_rel_Grp,
  mr_rel_conversep = Lazy.map f mr_rel_conversep,
  mr_rel_OO = Lazy.map f mr_rel_OO,
  mr_rel_OO_Grp = Lazy.map f mr_rel_OO_Grp,
  mr_rel_transfer = Lazy.map f mr_rel_transfer,
  mr_rel_id = Lazy.map f mr_rel_id,
  mr_rel_set = Lazy.map (map f) mr_rel_set};

val morph_mr_facts = map_mr_facts o Morphism.thm;

type nonemptiness_witness = {
  I: int list,
  wit: term,
  prop: thm list
};

fun mk_witness (I, wit) prop = {I = I, wit = wit, prop = prop};
fun map_witness f g {I, wit, prop} = {I = I, wit = f wit, prop = map g prop};
fun morph_witness phi = map_witness (Morphism.term phi) (Morphism.thm phi);

datatype var_type = Live_Var | Bound_Var | Free_Var | Dead_Var;
fun var_type_ord (Live_Var, Live_Var) = EQUAL
  | var_type_ord (Live_Var, _) = GREATER
  | var_type_ord (_, Live_Var) = LESS
  | var_type_ord (Free_Var, Free_Var) = EQUAL
  | var_type_ord (Free_Var, _) = GREATER
  | var_type_ord (_, Free_Var) = LESS
  | var_type_ord (Bound_Var, Bound_Var) = EQUAL
  | var_type_ord (Bound_Var, _) = GREATER
  | var_type_ord (_, Bound_Var) = LESS
  | var_type_ord (Dead_Var, Dead_Var) = EQUAL

datatype mrbnf = MRBNF of {
  name: binding,
  T: typ,
  var_types: var_type list,
  free: int,
  frees: typ list,
  bound: int,
  bounds: typ list,
  live: int,
  lives: typ list, (*source type variables of map*)
  lives': typ list, (*target type variables of map*)
  dead: int,
  deads: typ list,
  map: term,
  sets: term list,
  bd: term,
  class: sort,
  class_thms: class_thms,
  coclass: sort,
  axioms: axioms,
  defs: defs,
  facts: facts,
  mr_facts: mr_facts,
  nwits: int,
  wits: nonemptiness_witness list,
  rel: term,
  mr_rel: term,
  pred: term
};

(* getters *)

fun rep_mrbnf (MRBNF mrbnf) = mrbnf;
val name_of_mrbnf = #name o rep_mrbnf;
val T_of_mrbnf = #T o rep_mrbnf;
fun mk_T_of_mrbnf Ds Ts Bs Fs mrbnf =
  let val mrbnf_rep = rep_mrbnf mrbnf
  in Term.typ_subst_atomic ((#deads mrbnf_rep ~~ Ds) @ (#lives mrbnf_rep ~~ Ts) @
    (#bounds mrbnf_rep ~~ Bs) @ (#frees mrbnf_rep ~~ Fs)) (#T mrbnf_rep) end;
val var_types_of_mrbnf = #var_types o rep_mrbnf;
val free_of_mrbnf = #free o rep_mrbnf;
val frees_of_mrbnf = #frees o rep_mrbnf;
val bound_of_mrbnf = #bound o rep_mrbnf;
val bounds_of_mrbnf = #bounds o rep_mrbnf;
val live_of_mrbnf = #live o rep_mrbnf;
val lives_of_mrbnf = #lives o rep_mrbnf;
val lives'_of_mrbnf = #lives' o rep_mrbnf;
val dead_of_mrbnf = #dead o rep_mrbnf;
val deads_of_mrbnf = #deads o rep_mrbnf;
val class_of_mrbnf = #class o rep_mrbnf;
val class_thms_of_mrbnf = #class_thms o rep_mrbnf;
val coclass_of_mrbnf = #coclass o rep_mrbnf;
val axioms_of_mrbnf = #axioms o rep_mrbnf;
val facts_of_mrbnf = #facts o rep_mrbnf;
val mr_facts_of_mrbnf = #mr_facts o rep_mrbnf;
val nwits_of_mrbnf = #nwits o rep_mrbnf;
val wits_of_mrbnf = #wits o rep_mrbnf;

fun flatten_type_args_of_mrbnf mrbnf dead_x live_xs bound_xs free_xs =
  let
    val Ts = T_of_mrbnf mrbnf |> dest_Type |> snd;
    val frees = frees_of_mrbnf mrbnf;
    val bounds = bounds_of_mrbnf mrbnf;
    val lives = lives_of_mrbnf mrbnf;
    val deads = deads_of_mrbnf mrbnf;
  in
    permute_like_unique (op =) (deads @ lives @ bounds @ frees) Ts
      (replicate (length deads) dead_x @ live_xs @ bound_xs @ free_xs)
  end;

fun interlace _ _ _ [] = []
  | interlace (a :: als) bs fs (Live_Var::ts) = a :: interlace als bs fs ts
  | interlace als (b::bs) fs (Bound_Var::ts) = b :: interlace als bs fs ts
  | interlace als bs (f::fs) (Free_Var::ts) = f :: interlace als bs fs ts

fun deinterlace [] _ = ([], [], [])
  | deinterlace (x :: xs) (Live_Var::ts) = let val (a, b, c) = deinterlace xs ts in (x::a, b, c) end
  | deinterlace (x :: xs) (Bound_Var::ts) = let val (a, b, c) = deinterlace xs ts in (a, x::b, c) end
  | deinterlace (x :: xs) (Free_Var::ts) = let val (a, b, c) = deinterlace xs ts in (a, b, x::c) end

(*terms*)
val map_of_mrbnf = #map o rep_mrbnf;
val sets_of_mrbnf = #sets o rep_mrbnf;
fun mk_map_of_mrbnf Ds Ts Us Bs Fs mrbnf =
  let val mrbnf_rep = rep_mrbnf mrbnf;
  in
    Term.subst_atomic_types
      ((#deads mrbnf_rep ~~ Ds) @ (#lives mrbnf_rep ~~ Ts) @ (#lives' mrbnf_rep ~~ Us) @
        (#bounds mrbnf_rep ~~ Bs) @ (#frees mrbnf_rep ~~ Fs)) (#map mrbnf_rep)
  end;
fun mk_sets_of_mrbnf Dss Tss Bss Fss mrbnf =
  let val mrbnf_rep = rep_mrbnf mrbnf;
  fun assemble (((Ds, Ts), Bs), Fs)  = let
    val deads = #deads mrbnf_rep ~~ Ds;
    val _ = if length (#lives mrbnf_rep) <> length Ts then @{print} "lives length doesn't match" else ""
    val lives = #lives mrbnf_rep ~~Ts;
    val bounds = #bounds mrbnf_rep ~~ Bs;

    val frees = #frees mrbnf_rep ~~ Fs;

    in Term.subst_atomic_types (deads @ lives @ bounds @ frees) end;
  in
    (*map2 (fn (((Ds, Ts), Bs), Fs) => Term.subst_atomic_types
      ((#deads mrbnf_rep ~~ Ds) @ (#lives mrbnf_rep ~~ Ts) @ (#bounds mrbnf_rep ~~ Bs) @
        (#frees mrbnf_rep ~~ Fs))) (Dss ~~ Tss ~~ Bss ~~ Fss) (#sets mrbnf_rep)*)
    map2 assemble (Dss ~~ Tss ~~ Bss ~~ Fss) (#sets mrbnf_rep)
  end;

(*
fun mk_lab_sets_of_mrbnf Dss Tss Bss Fss mrbnf =
  let val mrbnf_rep = rep_mrbnf mrbnf;
  in
    map2 (fn (((Ds, Ts), Bs), Fs) => Term.subst_atomic_types
      ((#deads mrbnf_rep ~~ Ds) @ (#lives mrbnf_rep ~~ Ts) @ (#bounds mrbnf_rep ~~ Bs) @
        (#frees mrbnf_rep ~~ Fs))) (Dss ~~ Tss ~~ Bss ~~ Fss) (#sets mrbnf_rep)
  end;
*)

val bd_of_mrbnf = #bd o rep_mrbnf;
fun mk_bd_of_mrbnf Ds Bs Fs mrbnf =
  let val mrbnf_rep = rep_mrbnf mrbnf;
  in
    Term.subst_atomic_types ((#deads mrbnf_rep ~~ Ds) @ (#bounds mrbnf_rep ~~ Bs) @
      (#frees mrbnf_rep ~~ Fs)) (#bd mrbnf_rep)
  end;
fun mk_wits_of_mrbnf Dss Tss Bss Fss mrbnf =
  let
    val mrbnf_rep = rep_mrbnf mrbnf;
    val wits = map (fn x => (#I x, #wit x)) (#wits mrbnf_rep);
  in
    map2 (fn (((Ds, Ts), Bs), Fs) => apsnd (Term.subst_atomic_types
      ((#deads mrbnf_rep ~~ Ds) @ (#lives mrbnf_rep ~~ Ts) @ (#bounds mrbnf_rep ~~ Bs) @
        (#frees mrbnf_rep ~~ Fs)))) (Dss ~~ Tss ~~ Bss ~~ Fss) wits
  end;
val rel_of_mrbnf = #rel o rep_mrbnf;
fun mk_rel_of_mrbnf Ds Ts Us Bs Fs mrbnf =
  let val mrbnf_rep = rep_mrbnf mrbnf;
  in
    Term.subst_atomic_types
      ((#deads mrbnf_rep ~~ Ds) @ (#lives mrbnf_rep ~~ Ts) @ (#lives' mrbnf_rep ~~ Us) @
        (#bounds mrbnf_rep ~~ Bs) @ (#frees mrbnf_rep ~~ Fs)) (#rel mrbnf_rep)
  end;
val mr_rel_of_mrbnf = #mr_rel o rep_mrbnf;
fun mk_mr_rel_of_mrbnf Ds Ts Us Bs Fs mrbnf =
  let val mrbnf_rep = rep_mrbnf mrbnf;
  in
    Term.subst_atomic_types
      ((#deads mrbnf_rep ~~ Ds) @ (#lives mrbnf_rep ~~ Ts) @ (#lives' mrbnf_rep ~~ Us) @
        (#bounds mrbnf_rep ~~ Bs) @ (#frees mrbnf_rep ~~ Fs)) (#mr_rel mrbnf_rep)
  end;
val pred_of_mrbnf = #pred o rep_mrbnf;
fun mk_pred_of_mrbnf Ds Ts Bs Fs mrbnf =
  let val mrbnf_rep = rep_mrbnf mrbnf;
  in
    Term.subst_atomic_types
      ((#deads mrbnf_rep ~~ Ds) @ (#lives mrbnf_rep ~~ Ts) @ (#bounds mrbnf_rep ~~ Bs) @
        (#frees mrbnf_rep ~~ Fs)) (#pred mrbnf_rep)
  end;

fun mk_map_comb_of_mrbnf Ds fs gs hs mrbnf =
  let
    val (As, As') = split_list (map (dest_funT o fastype_of) fs)
    val Bs = map (fst o dest_funT o fastype_of) gs
    val Fs = map (fst o dest_funT o fastype_of) hs
  in Term.list_comb (
    mk_map_of_mrbnf Ds As As' Bs Fs mrbnf,
    interlace fs gs hs (var_types_of_mrbnf mrbnf)
  ) end;

(*thms*)
val bd_infinite_regular_card_order_of_mrbnf = #bd_infinite_regular_card_order o #axioms o rep_mrbnf;
val bd_Card_order_of_mrbnf = #bd_Card_order o #facts o rep_mrbnf;
val bd_Cinfinite_of_mrbnf = #bd_Cinfinite o #facts o rep_mrbnf;
val bd_Cnotzero_of_mrbnf = #bd_Cnotzero o #facts o rep_mrbnf;
val bd_card_order_of_mrbnf = #bd_card_order o #facts o rep_mrbnf;
val bd_cinfinite_of_mrbnf = #bd_cinfinite o #facts o rep_mrbnf;
val bd_regularCard_of_mrbnf = #bd_regularCard o #facts o rep_mrbnf;
val collect_set_map_of_mrbnf = Lazy.force o #collect_set_map o #facts o rep_mrbnf;
val in_bd_of_mrbnf = Lazy.force o #in_bd o #facts o rep_mrbnf;
val in_cong_of_mrbnf = Lazy.force o #in_cong o #facts o rep_mrbnf;
val in_mono_of_mrbnf = Lazy.force o #in_mono o #facts o rep_mrbnf;
val in_rel_of_mrbnf = Lazy.force o #in_rel o #facts o rep_mrbnf;
val inj_map_of_mrbnf = Lazy.force o #inj_map o #facts o rep_mrbnf;
val inj_map_strong_of_mrbnf = Lazy.force o #inj_map_strong o #facts o rep_mrbnf;
val le_rel_OO_of_mrbnf = #le_rel_OO o #axioms o rep_mrbnf;
val map_comp0_of_mrbnf = #map_comp0 o #axioms o rep_mrbnf;
val map_comp_of_mrbnf = Lazy.force o #map_comp o #facts o rep_mrbnf;
val map_cong0_of_mrbnf = #map_cong0 o #axioms o rep_mrbnf;
val map_cong_of_mrbnf = Lazy.force o #map_cong o #facts o rep_mrbnf;
val map_cong_pred_of_mrbnf = Lazy.force o #map_cong_pred o #facts o rep_mrbnf;
val map_cong_simp_of_mrbnf = Lazy.force o #map_cong_simp o #facts o rep_mrbnf;
val map_def_of_mrbnf = #map_def o #defs o rep_mrbnf;
val map_id0_of_mrbnf = #map_id0 o #axioms o rep_mrbnf;
val map_id_of_mrbnf = Lazy.force o #map_id o #facts o rep_mrbnf;
val map_ident0_of_mrbnf = Lazy.force o #map_ident0 o #facts o rep_mrbnf;
val map_ident_of_mrbnf = Lazy.force o #map_ident o #facts o rep_mrbnf;
val map_transfer_of_mrbnf = Lazy.force o #map_transfer o #facts o rep_mrbnf;
val rel_eq_onp_of_mrbnf = Lazy.force o #rel_eq_onp o #facts o rep_mrbnf;
val pred_def_of_mrbnf = #pred_def o #defs o rep_mrbnf;
val pred_map_of_mrbnf = Lazy.force o #pred_map o #facts o rep_mrbnf;
val pred_mono_strong0_of_mrbnf = Lazy.force o #pred_mono_strong0 o #facts o rep_mrbnf;
val pred_mono_strong_of_mrbnf = Lazy.force o #pred_mono_strong o #facts o rep_mrbnf;
val pred_mono_of_mrbnf = Lazy.force o #pred_mono o #facts o rep_mrbnf;
val pred_cong0_of_mrbnf = Lazy.force o #pred_cong0 o #facts o rep_mrbnf;
val pred_cong_of_mrbnf = Lazy.force o #pred_cong o #facts o rep_mrbnf;
val pred_cong_simp_of_mrbnf = Lazy.force o #pred_cong_simp o #facts o rep_mrbnf;
val pred_rel_of_mrbnf = Lazy.force o #pred_rel o #facts o rep_mrbnf;
val pred_set_of_mrbnf = #pred_set o #axioms o rep_mrbnf;
val pred_transfer_of_mrbnf = Lazy.force o #pred_transfer o #facts o rep_mrbnf;
val pred_True_of_mrbnf = Lazy.force o #pred_True o #facts o rep_mrbnf;
val rel_Grp_of_mrbnf = Lazy.force o #rel_Grp o #facts o rep_mrbnf;
val rel_OO_Grp_of_mrbnf = #rel_OO_Grp o #axioms o rep_mrbnf;
val rel_OO_of_mrbnf = Lazy.force o #rel_OO o #facts o rep_mrbnf;
val rel_OO_Grp_id_of_mrbnf = Lazy.force o #rel_OO_Grp_id o #facts o rep_mrbnf;
val rel_cong0_of_mrbnf = Lazy.force o #rel_cong0 o #facts o rep_mrbnf;
val rel_cong_of_mrbnf = Lazy.force o #rel_cong o #facts o rep_mrbnf;
val rel_cong_simp_of_mrbnf = Lazy.force o #rel_cong_simp o #facts o rep_mrbnf;
val rel_conversep_of_mrbnf = Lazy.force o #rel_conversep o #facts o rep_mrbnf;
val rel_def_of_mrbnf = #rel_def o #defs o rep_mrbnf;
val rel_eq_of_mrbnf = Lazy.force o #rel_eq o #facts o rep_mrbnf;
val rel_flip_of_mrbnf = Lazy.force o #rel_flip o #facts o rep_mrbnf;
val rel_map_of_mrbnf = Lazy.force o #rel_map o #facts o rep_mrbnf;
val rel_mono_of_mrbnf = Lazy.force o #rel_mono o #facts o rep_mrbnf;
val rel_mono_strong0_of_mrbnf = Lazy.force o #rel_mono_strong0 o #facts o rep_mrbnf;
val rel_mono_strong_of_mrbnf = Lazy.force o #rel_mono_strong o #facts o rep_mrbnf;
val rel_refl_of_mrbnf = Lazy.force o #rel_refl o #facts o rep_mrbnf;
val rel_refl_strong_of_mrbnf = Lazy.force o #rel_refl_strong o #facts o rep_mrbnf;
val rel_reflp_of_mrbnf = Lazy.force o #rel_reflp o #facts o rep_mrbnf;
val rel_symp_of_mrbnf = Lazy.force o #rel_symp o #facts o rep_mrbnf;
val rel_transfer_of_mrbnf = Lazy.force o #rel_transfer o #facts o rep_mrbnf;
val rel_transp_of_mrbnf = Lazy.force o #rel_transp o #facts o rep_mrbnf;
val set_bd_of_mrbnf = #set_bd o #axioms o rep_mrbnf;
val set_defs_of_mrbnf = #set_defs o #defs o rep_mrbnf;
val set_map0_of_mrbnf = #set_map0 o #axioms o rep_mrbnf;
val set_map_of_mrbnf = map Lazy.force o #set_map o #facts o rep_mrbnf;
val set_bd_UNIV_of_mrbnf = map Lazy.force o #set_bd_UNIV o #facts o rep_mrbnf;
val set_transfer_of_mrbnf = Lazy.force o #set_transfer o #facts o rep_mrbnf;
val wit_thms_of_mrbnf = maps #prop o wits_of_mrbnf;
val wit_thmss_of_mrbnf = map #prop o wits_of_mrbnf;

val var_large_of_mrbnf = #var_large o #mr_facts o rep_mrbnf;
val var_regular_of_mrbnf = #var_regular o #mr_facts o rep_mrbnf;
val natLeq_bound_of_mrbnf = #natLeq_bound o #mr_facts o rep_mrbnf;
val UNIV_cinfinite_of_mrbnf = #UNIV_cinfinite o #mr_facts o rep_mrbnf;
val supp_comp_bound_of_mrbnf = #supp_comp_bound o #mr_facts o rep_mrbnf;
val Un_bound_of_mrbnf = #Un_bound o #mr_facts o rep_mrbnf;
val UNION_bound_of_mrbnf = #UNION_bound o #mr_facts o rep_mrbnf;
val mr_rel_cong0_of_mrbnf = Lazy.force o #mr_rel_cong0 o #mr_facts o rep_mrbnf;
val mr_rel_cong_of_mrbnf = Lazy.force o #mr_rel_cong o #mr_facts o rep_mrbnf;
val mr_in_rel_of_mrbnf = Lazy.force o #mr_in_rel o #mr_facts o rep_mrbnf;
val mr_le_rel_OO_of_mrbnf = Lazy.force o #mr_le_rel_OO o #mr_facts o rep_mrbnf;
val mr_map_transfer_of_mrbnf = Lazy.force o #mr_map_transfer o #mr_facts o rep_mrbnf;
val mr_rel_Grp_of_mrbnf = Lazy.force o #mr_rel_Grp o #mr_facts o rep_mrbnf;
val mr_rel_OO_Grp_of_mrbnf = Lazy.force o #mr_rel_OO_Grp o #mr_facts o rep_mrbnf;
val mr_rel_OO_of_mrbnf = Lazy.force o #mr_rel_OO o #mr_facts o rep_mrbnf;
val mr_rel_conversep_of_mrbnf = Lazy.force o #mr_rel_conversep o #mr_facts o rep_mrbnf;
val mr_rel_def_of_mrbnf = #mr_rel_def o #defs o rep_mrbnf;
val mr_rel_eq_of_mrbnf = Lazy.force o #mr_rel_eq o #mr_facts o rep_mrbnf;
val mr_rel_flip_of_mrbnf = Lazy.force o #mr_rel_flip o #mr_facts o rep_mrbnf;
val mr_rel_map_of_mrbnf = Lazy.force o #mr_rel_map o #mr_facts o rep_mrbnf;
val mr_rel_mono_of_mrbnf = Lazy.force o #mr_rel_mono o #mr_facts o rep_mrbnf;
val mr_rel_mono_strong0_of_mrbnf = Lazy.force o #mr_rel_mono_strong0 o #mr_facts o rep_mrbnf;
val mr_rel_mono_strong_of_mrbnf = Lazy.force o #mr_rel_mono_strong o #mr_facts o rep_mrbnf;
val mr_rel_transfer_of_mrbnf = Lazy.force o #mr_rel_transfer o #mr_facts o rep_mrbnf;
val mr_set_transfer_of_mrbnf = Lazy.force o #mr_set_transfer o #mr_facts o rep_mrbnf;
val mr_rel_id_of_mrbnf = Lazy.force o #mr_rel_id o #mr_facts o rep_mrbnf;
val mr_rel_set_of_mrbnf = Lazy.force o #mr_rel_set o #mr_facts o rep_mrbnf;

fun mk_mrbnf name T var_types free frees bound bounds live lives lives' dead deads map sets bd class class_thms coclass axioms
  defs facts mr_facts wits rel mr_rel pred = MRBNF {name = name, T = T, var_types = var_types,
       free = free, frees = frees, bound = bound, bounds = bounds,
       live = live, lives = lives, lives' = lives', dead = dead, deads = deads,
       map = map, sets = sets, bd = bd, class = class, class_thms = class_thms, coclass = coclass,
       axioms = axioms, defs = defs, facts = facts, mr_facts = mr_facts,
       nwits = length wits, wits = wits, rel = rel, mr_rel = mr_rel, pred = pred};

fun map_mrbnf f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
  (MRBNF {name = name, T = T, var_types = var_types, free = free, frees = frees, bound = bound, bounds = bounds,
  live = live, lives = lives, lives' = lives',
  dead = dead, deads = deads, map = map, sets = sets, bd = bd, class = class, class_thms = class_thms, coclass = coclass,
  axioms = axioms, defs = defs, facts = facts, mr_facts = mr_facts,
  nwits = nwits, wits = wits, rel = rel, mr_rel = mr_rel, pred = pred}) =
  MRBNF {name = f1 name, T = f2 T, var_types = var_types,
       free = f3 free, frees = f4 frees, bound = f5 bound, bounds = f6 bounds,
       live = f7 live, lives = f8 lives, lives' = f9 lives', dead = f10 dead, deads = f11 deads,
       map = f12 map, sets = f13 sets, bd = f14 bd, class = f15 class, class_thms = f16 class_thms, coclass = f17 coclass,
       axioms = f18 axioms, defs = f19 defs, facts = f20 facts, mr_facts = f21 mr_facts,
       nwits = f22 nwits, wits = f23 wits, rel = f24 rel, mr_rel = f25 mr_rel, pred = f26 pred};

fun morph_mrbnf phi =
  let
    val Tphi = Morphism.typ phi;
    val tphi = Morphism.term phi;
  in
    map_mrbnf (Morphism.binding phi) Tphi I (map Tphi) I (map Tphi) I (map Tphi) (map Tphi) I
      (map Tphi) tphi (map tphi) tphi I I I (morph_axioms phi) (morph_defs phi) (morph_facts phi)
      (morph_mr_facts phi) I (map (morph_witness phi)) tphi tphi tphi
  end;

fun morph_mrbnf_defs phi = map_mrbnf I I I I I I I I I I I I I I I I I I (morph_defs phi) I I I I I I I;

fun permute_deads perm = map_mrbnf I I I I I I I I I I perm I I I I I I I I I I I I I I I;

val transfer_mrbnf = morph_mrbnf o Morphism.transfer_morphism;

structure Data = Generic_Data
(
  type T = mrbnf Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun mrbnf_of_generic context =
  Option.map (transfer_mrbnf (Context.theory_of context)) o Symtab.lookup (Data.get context);

val mrbnf_of = mrbnf_of_generic o Context.Proof;
val mrbnf_of_global = mrbnf_of_generic o Context.Theory;

(* Utilities *)

fun normalize_set insts instA set =
  let
    val (T, T') = dest_funT (fastype_of set);
    val A = fst (Term.dest_TVar (HOLogic.dest_setT T'));
    val params = Term.add_tvar_namesT T [];
  in Term.subst_TVars ((A :: params) ~~ (instA :: insts)) set end;

fun normalize_rel ctxt instTs instA instB rel =
  let
    val thy = Proof_Context.theory_of ctxt;
    val tyenv =
      Sign.typ_match thy (fastype_of rel, Library.foldr (op -->) (instTs, mk_pred2T instA instB))
        Vartab.empty;
  in Envir.subst_term (tyenv, Vartab.empty) rel end
  handle Type.TYPE_MATCH => error "Bad relator";

fun normalize_pred ctxt instTs instA pred =
  let
    val thy = Proof_Context.theory_of ctxt;
    val tyenv =
      Sign.typ_match thy (fastype_of pred, Library.foldr (op -->) (instTs, mk_pred1T instA))
        Vartab.empty;
  in Envir.subst_term (tyenv, Vartab.empty) pred end
  handle Type.TYPE_MATCH => error "Bad predicator";

fun normalize_wit insts CA As wit =
  let
    fun strip_param (Ts, T as Type (@{type_name fun}, [T1, T2])) =
        if Type.raw_instance (CA, T) then (Ts, T) else strip_param (T1 :: Ts, T2)
      | strip_param x = x;
    val (Ts, T) = strip_param ([], fastype_of wit);
    val subst = Term.add_tvar_namesT T [] ~~ insts;
    fun find y = find_index (fn x => x = y) As;
  in
    (map (find o Term.typ_subst_TVars subst) (rev Ts), Term.subst_TVars subst wit)
  end;

fun minimize_wits wits =
 let
   fun minimize done [] = done
     | minimize done ((I, wit) :: todo) =
       if exists (fn (J, _) => subset (op =) (J, I)) (done @ todo)
       then minimize done todo
       else minimize ((I, wit) :: done) todo;
 in minimize [] wits end;

fun mk_map live bound free Ts Us t =
  let
    val (Ts0, Us0) = strip_typeN (live + bound + free + 1) (fastype_of t)
      |>> List.last
      |> apply2 (snd o dest_Type)
  in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun mk_pred Ts t =
  let val Ts0 = domain_type (body_fun_type (fastype_of t)) |> snd o dest_Type in
    Term.subst_atomic_types (Ts0 ~~ Ts) t
  end;
val mk_set = mk_pred;

fun mk_rel live (_ : int) (_ : int) Ts Us t =
  let
    val (Ts0, Us0) = case binder_types
      (snd (strip_typeN live (fastype_of t))) of
        [Type (_, Ts0), Type (_, Us0)] => (Ts0, Us0)
        | _ => raise Match;
  in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun mk_mr_rel live bound free Ts Us t =
  let
    val (Ts0, Us0) = case binder_types
      (snd (strip_typeN (live + bound + free) (fastype_of t))) of
        [Type (_, Ts0), Type (_, Us0)] => (Ts0, Us0)
        | _ => raise Match;
  in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun build_map_or_rel lives_only mk const of_mrbnf dest pre_cst_table ctxt simple_Ts simple_Us
  build_simple =
  let
    fun build (TU as (T, U)) =
      if exists (curry (op =) T) simple_Ts orelse exists (curry (op =) U) simple_Us then
        build_simple TU
      else if T = U andalso not (exists_subtype_in simple_Ts T) andalso
          not (exists_subtype_in simple_Us U) then
        const T
      else
        (case TU of
          (Type (s, Ts), Type (s', Us)) =>
          if s = s' then
            let
              fun recurse (live, bound, free, cst0) =
                let
                  val cst = mk live bound free Ts Us cst0;
                  val TUs' = map dest (fst (strip_typeN
                    (live + (if lives_only then 0 else bound + free)) (fastype_of cst)));
                in Term.list_comb (cst, map build TUs') end;
            in
              (case AList.lookup (op =) pre_cst_table s of
                NONE =>
                (case mrbnf_of ctxt s of
                  SOME mrbnf => recurse
                    (live_of_mrbnf mrbnf, bound_of_mrbnf mrbnf, free_of_mrbnf mrbnf, of_mrbnf mrbnf)
                | NONE => build_simple TU)
              | SOME entry => recurse entry)
            end
          else
            build_simple TU
        | _ => build_simple TU);
  in build end;

val build_map = build_map_or_rel false mk_map HOLogic.id_const map_of_mrbnf dest_funT
  [(@{type_name set}, (1, 0, 0, @{term image}))];
val build_rel = build_map_or_rel true mk_rel HOLogic.eq_const rel_of_mrbnf dest_pred2T o append
  [(@{type_name set}, (1, 0, 0, @{term rel_set})), (@{type_name fun}, (2, 0, 0, @{term rel_fun}))];
val build_mr_rel = build_map_or_rel false mk_mr_rel HOLogic.eq_const mr_rel_of_mrbnf dest_pred2T
  o append [(@{type_name set}, (1, 0, 0, @{term rel_set})),
    (@{type_name fun}, (2, 0, 0, @{term rel_fun}))];

fun build_set ctxt A =
  let
    fun build T =
      Abs (Name.uu, T,
        if T = A then
          HOLogic.mk_set A [Bound 0]
        else
          (case T of
            Type (s, Ts) =>
            let
              val sets = map (mk_set Ts) (sets_of_mrbnf (the (mrbnf_of ctxt s)))
                |> filter (exists_subtype_in [A] o range_type o fastype_of);
              val set_apps = map (fn set => Term.betapply (set, Bound 0)) sets;

              fun recurse set_app =
                let
                  val elemT = case fastype_of set_app of
                    Type (@{type_name set}, [elemT]) => elemT
                    | _ => raise Match;
                in
                  if elemT = A then set_app else mk_UNION set_app (build elemT)
                end;
            in
              if null set_apps then HOLogic.mk_set A []
              else Library.foldl1 mk_union (map recurse set_apps)
            end
          | _ => HOLogic.mk_set A []));
  in build end;

fun map_flattened_map_args ctxt s map_args live_fs bound_fs free_fs =
  let
    val flat_fs = flatten_type_args_of_mrbnf (the (mrbnf_of ctxt s)) Term.dummy live_fs bound_fs
      free_fs;
    val flat_fs' = map_args flat_fs;
  in
    permute_like_unique (op aconv) flat_fs (live_fs @ bound_fs @ free_fs) flat_fs'
  end;


(* Names *)

val mapN = "map";
val setN = "set";
fun mk_setN i = setN ^ nonzero_string_of_int i;
val bdN = "bd";
val witN = "wit";
fun mk_witN i = witN ^ nonzero_string_of_int i;
val relN = "rel";
val mr_relN = "mr_rel";
val predN = "pred";

val var_typeN = "var";
val covar_typeN = "covar";
val covar_witN = "wit_" ^ covar_typeN;
val var_type_class_ass1N = "large";
val var_type_class_ass2N = "regular";

val bd_infinite_regular_card_orderN = "bd_infinite_regular_card_order";
val bd_Card_orderN = "bd_Card_order";
val bd_CinfiniteN = "bd_Cinfinite";
val bd_CnotzeroN = "bd_Cnotzero";
val bd_card_orderN = "bd_card_order";
val bd_cinfiniteN = "bd_cinfinite";
val bd_regularCardN = "bd_regularCard";
val collect_set_mapN = "collect_set_map";
val in_bdN = "in_bd";
val in_monoN = "in_mono";
val in_relN = "in_rel";
val inj_mapN = "inj_map";
val inj_map_strongN = "inj_map_strong";
val map_comp0N = "map_comp0";
val map_compN = "map_comp";
val map_cong0N = "map_cong0";
val map_congN = "map_cong";
val map_cong_idN = "map_cong_id";
val map_cong_simpN = "map_cong_simp";
val map_cong_predN = "map_cong_pred";
val map_id0N = "map_id0";
val map_idN = "map_id";
val map_identN = "map_ident";
val map_transferN = "map_transfer";
val pred_mono_strong0N = "pred_mono_strong0";
val pred_mono_strongN = "pred_mono_strong";
val pred_monoN = "pred_mono";
val pred_transferN = "pred_transfer";
val pred_TrueN = "pred_True";
val pred_mapN = "pred_map";
val pred_relN = "pred_rel";
val pred_setN = "pred_set";
val pred_congN = "pred_cong";
val pred_cong_simpN = "pred_cong_simp";
val rel_GrpN = "rel_Grp";
val rel_comppN = "rel_compp";
val rel_compp_GrpN = "rel_compp_Grp";
val rel_congN = "rel_cong";
val rel_cong_simpN = "rel_cong_simp";
val rel_conversepN = "rel_conversep";
val rel_eqN = "rel_eq";
val rel_eq_onpN = "rel_eq_onp";
val rel_flipN = "rel_flip";
val rel_mapN = "rel_map";
val rel_monoN = "rel_mono";
val rel_mono_strong0N = "rel_mono_strong0";
val rel_mono_strongN = "rel_mono_strong";
val rel_reflN = "rel_refl";
val rel_refl_strongN = "rel_refl_strong";
val rel_reflpN = "rel_reflp";
val rel_sympN = "rel_symp";
val rel_transferN = "rel_transfer";
val rel_transpN = "rel_transp";
val set_bdN = "set_bd";
val set_map0N = "set_map0";
val set_mapN = "set_map";
val set_bd_UNIVN = "set_bd_UNIV";
val set_transferN = "set_transfer";

val var_largeN = var_typeN ^ "_" ^ var_type_class_ass1N;
val var_regularN = var_typeN ^ "_" ^ var_type_class_ass2N;
val natLeq_boundN = "natLeq_bound";
val UNIV_cinfiniteN = "UNIV_cinfinite";
val supp_comp_boundN = "supp_comp_bound";
val Un_boundN = "Un_bound";
val UNION_boundN = "UN_bound";
val mr_rel_congN = "mr_rel_cong";
val mr_in_relN = "mr_in_rel";
val mr_le_rel_OON = "mr_le_rel_OO";
val mr_map_transferN = "mr_map_transfer";
val mr_rel_eqN = "mr_rel_eq";
val mr_rel_flipN = "mr_rel_flip";
val mr_rel_mapN = "mr_rel_map";
val mr_rel_monoN = "mr_rel_mono";
val mr_rel_mono_strong0N = "mr_rel_mono_strong0";
val mr_rel_mono_strongN = "mr_rel_mono_strong";
val mr_set_transferN = "mr_set_transfer";
val mr_rel_GrpN = "mr_rel_Grp";
val mr_rel_conversepN = "mr_rel_conversep";
val mr_rel_OON = "mr_rel_OO";
val mr_rel_OO_GrpN = "mr_rel_OO_Grp";
val mr_rel_transferN = "mr_rel_transfer";
val mr_rel_idN = "mr_rel_id";
val mr_rel_setN = "mr_rel_set";

datatype inline_policy = Dont_Inline | Hardly_Inline | Smart_Inline | Do_Inline;

datatype fact_policy = Dont_Note | Note_Some | Note_All;

val mrbnf_internals = Attrib.setup_config_bool @{binding mrbnf_internals} (K false);
val mrbnf_verbose = Attrib.setup_config_bool @{binding mrbnf_verbose} (K false);
val mrbnf_notes = Attrib.setup_config_bool @{binding mrbnf_notes} (K true);
val mrbnf_timing = Attrib.setup_config_bool @{binding mrbnf_timing} (K false);

fun user_policy policy ctxt = if Config.get ctxt mrbnf_notes then
  (if Config.get ctxt mrbnf_internals then Note_All else policy)
  else Dont_Note;

val smart_max_inline_term_size = 25; (*FUDGE*)

fun note_mrbnf_thms fact_policy qualify0 mrbnf_b mrbnf lthy =
  let
    val axioms = axioms_of_mrbnf mrbnf;
    val facts = facts_of_mrbnf mrbnf;
    val mr_facts = mr_facts_of_mrbnf mrbnf;
    val wits = wits_of_mrbnf mrbnf;
    val live = live_of_mrbnf mrbnf;
    val bound = bound_of_mrbnf mrbnf;
    val free = free_of_mrbnf mrbnf;
    val var_types = var_types_of_mrbnf mrbnf;
    val qualify =
      let val qs = Binding.path_of mrbnf_b;
      in fold_rev (fn (s, mand) => Binding.qualify mand s) qs #> qualify0 end;

    fun note_if_note_all (noted0, lthy0) =
      let
        val witNs = if length wits = 1 then [witN] else map mk_witN (1 upto length wits);
        val notes =
          [(bd_infinite_regular_card_orderN, [#bd_infinite_regular_card_order axioms]),
           (bd_card_orderN, [#bd_card_order facts]),
           (bd_cinfiniteN, [#bd_cinfinite facts]),
           (bd_regularCardN, [#bd_regularCard facts]),
           (bd_Card_orderN, [#bd_Card_order facts]),
           (bd_CinfiniteN, [#bd_Cinfinite facts]),
           (bd_CnotzeroN, [#bd_Cnotzero facts]),
           (collect_set_mapN, [Lazy.force (#collect_set_map facts)]),
           (in_bdN, [Lazy.force (#in_bd facts)]),
           (in_monoN, [Lazy.force (#in_mono facts)]),
           (map_comp0N, [#map_comp0 axioms]),
           (rel_mono_strong0N, [Lazy.force (#rel_mono_strong0 facts)]),
           (pred_mono_strong0N, [Lazy.force (#pred_mono_strong0 facts)]),
           (set_map0N, #set_map0 axioms),
           (set_bd_UNIVN, map Lazy.force (#set_bd_UNIV facts)),
           (mr_in_relN, [Lazy.force (#mr_in_rel mr_facts)]),
           (mr_rel_eqN, [Lazy.force (#mr_rel_eq mr_facts)]),
           (mr_rel_mono_strongN, [Lazy.force (#mr_rel_mono_strong mr_facts)]),
           (mr_rel_conversepN, [Lazy.force (#mr_rel_conversep mr_facts)]),
           (mr_rel_OON, [Lazy.force (#mr_rel_OO mr_facts)]),
           (mr_rel_OO_GrpN, [Lazy.force (#mr_rel_OO_Grp mr_facts)]),
           (mr_rel_transferN, [Lazy.force (#mr_rel_transfer mr_facts)]),
           (mr_rel_setN, Lazy.force (#mr_rel_set mr_facts)),
           (var_largeN, [#var_large mr_facts]),
           (var_regularN, [#var_regular mr_facts])] @
          (witNs ~~ wit_thmss_of_mrbnf mrbnf)
          |> map (fn (thmN, thms) =>
            ((qualify (Binding.qualify true (Binding.name_of mrbnf_b) (Binding.name thmN)), []),
             [(thms, [])]));
      in
        Local_Theory.notes notes lthy0 |>> append noted0
      end;

    fun note_unless_dont_note (noted0, lthy0) =
      let
        fun interlace' a b c = interlace (replicate live a) (replicate bound b) (replicate free c) var_types
        val id_prems = flat (interlace' [] @{thms bij_id supp_id_bound} @{thms supp_id_bound});
        val prems = id_prems @ id_prems @ @{thms _}
          @ interlace' @{thm _} @{thm refl} @{thm refl};
        val notes =
          [(in_relN, [Lazy.force (#in_rel facts)], []),
           (inj_mapN, [Lazy.force (#inj_map facts)], []),
           (inj_map_strongN, [Lazy.force (#inj_map_strong facts)], []),
           (map_compN, [Lazy.force (#map_comp facts)], []),
           (map_cong0N, [#map_cong0 axioms], []),
           (map_congN, [Lazy.force (#map_cong facts)], []),
           (map_cong_idN, [Lazy.force (#map_cong facts) OF prems], fundefcong_attrs),
           (map_cong_simpN, [Lazy.force (#map_cong_simp facts)], []),
           (map_cong_predN, [Lazy.force (#map_cong_pred facts)], []),
           (map_idN, [Lazy.force (#map_id facts)], []),
           (map_id0N, [#map_id0 axioms], []),
           (map_transferN, [Lazy.force (#map_transfer facts)], []),
           (map_identN, [Lazy.force (#map_ident facts)], []),
           (pred_mono_strongN, [Lazy.force (#pred_mono_strong facts)], []),
           (pred_monoN, [Lazy.force (#pred_mono facts)], []),
           (pred_congN, [Lazy.force (#pred_cong facts)], fundefcong_attrs),
           (pred_cong_simpN, [Lazy.force (#pred_cong_simp facts)], []),
           (pred_mapN, [Lazy.force (#pred_map facts)], []),
           (pred_relN, [Lazy.force (#pred_rel facts)], []),
           (pred_transferN, [Lazy.force (#pred_transfer facts)], []),
           (pred_TrueN, [Lazy.force (#pred_True facts)], []),
           (pred_setN, [#pred_set axioms], []),
           (rel_comppN, [Lazy.force (#rel_OO facts)], []),
           (rel_compp_GrpN, no_refl [#rel_OO_Grp axioms], []),
           (rel_conversepN, [Lazy.force (#rel_conversep facts)], []),
           (rel_eqN, [Lazy.force (#rel_eq facts)], []),
           (rel_eq_onpN, [Lazy.force (#rel_eq_onp facts)], []),
           (rel_flipN, [Lazy.force (#rel_flip facts)], []),
           (rel_GrpN, [Lazy.force (#rel_Grp facts)], []),
           (rel_mapN, Lazy.force (#rel_map facts), []),
           (rel_monoN, [Lazy.force (#rel_mono facts)], mono_attrs),
           (rel_mono_strongN, [Lazy.force (#rel_mono_strong facts)], []),
           (rel_congN, [Lazy.force (#rel_cong facts)], fundefcong_attrs),
           (rel_cong_simpN, [Lazy.force (#rel_cong_simp facts)], []),
           (rel_reflN, [Lazy.force (#rel_refl facts)], []),
           (rel_refl_strongN, [Lazy.force (#rel_refl_strong facts)], []),
           (rel_reflpN, [Lazy.force (#rel_reflp facts)], []),
           (rel_sympN, [Lazy.force (#rel_symp facts)], []),
           (rel_transpN, [Lazy.force (#rel_transp facts)], []),
           (rel_transferN, [Lazy.force (#rel_transfer facts)], []),
           (set_mapN, map Lazy.force (#set_map facts), []),
           (set_transferN, Lazy.force (#set_transfer facts), []),
           (set_bdN, #set_bd axioms, []),
           (natLeq_boundN, [#natLeq_bound mr_facts], []),
           (UNIV_cinfiniteN, [#UNIV_cinfinite mr_facts], []),
           (supp_comp_boundN, [#supp_comp_bound mr_facts], []),
           (Un_boundN, [#Un_bound mr_facts], []),
           (UNION_boundN, [#UNION_bound mr_facts], []),
           (mr_le_rel_OON, [Lazy.force (#mr_le_rel_OO mr_facts)], []),
           (mr_rel_GrpN, [Lazy.force (#mr_rel_Grp mr_facts)], []),
           (mr_rel_congN, [Lazy.force (#mr_rel_cong mr_facts)], []),
           (mr_rel_flipN, [Lazy.force (#mr_rel_flip mr_facts)], []),
           (mr_rel_mapN, Lazy.force (#mr_rel_map mr_facts), []),
           (mr_rel_monoN, [Lazy.force (#mr_rel_mono mr_facts)], []),
           (mr_rel_mono_strong0N, [Lazy.force (#mr_rel_mono_strong0 mr_facts)], []),
           (mr_rel_idN, [Lazy.force (#mr_rel_id mr_facts)], []),
           (mr_map_transferN, [Lazy.force (#mr_map_transfer mr_facts)], []),
           (mr_set_transferN, Lazy.force (#mr_set_transfer mr_facts), [])]
          |> filter_out (null o #2)
          |> map (fn (thmN, thms, attrs) =>
            ((qualify (Binding.qualify true (Binding.name_of mrbnf_b) (Binding.name thmN)), attrs),
             [(thms, [])]));
      in
        Local_Theory.notes notes lthy0 |>> append noted0
      end;
  in
    ([], lthy)
    |> fact_policy = Note_All ? note_if_note_all
    |> fact_policy <> Dont_Note ? note_unless_dont_note
    |>> (fn [] => mrbnf | noted => morph_mrbnf (substitute_noted_thm noted) mrbnf)
  end;

fun note_mrbnf_defs mrbnf lthy =
  let
    fun mk_def_binding cst_of =
      Thm.def_binding (Binding.qualified_name (dest_Const (cst_of mrbnf) |> fst));
    val notes =
      [(mk_def_binding map_of_mrbnf, map_def_of_mrbnf mrbnf),
       (mk_def_binding rel_of_mrbnf, rel_def_of_mrbnf mrbnf),
       (mk_def_binding mr_rel_of_mrbnf, mr_rel_def_of_mrbnf mrbnf),
       (mk_def_binding pred_of_mrbnf, pred_def_of_mrbnf mrbnf)] @
      @{map 2} (pair o mk_def_binding o K) (sets_of_mrbnf mrbnf) (set_defs_of_mrbnf mrbnf)
      |> map (fn (b, thm) => ((b, []), [([thm], [])]));
  in
    lthy
    |> Local_Theory.notes notes
    |>> (fn noted => morph_mrbnf (substitute_noted_thm noted) mrbnf)
  end;

fun mk_wit_goals zs bs sets (I, wit) =
  let
    val xs = map (nth bs) I;
    fun wit_goal i =
      let
        val z = nth zs i;
        val set_wit = nth sets i $ Term.list_comb (wit, xs);
        val concl = HOLogic.mk_Trueprop
          (if member (op =) I i then HOLogic.mk_eq (z, nth bs i) else @{term False});
      in
        fold_rev Logic.all (z :: xs) (Logic.mk_implies (mk_Trueprop_mem (z, set_wit), concl))
      end;
  in
    map wit_goal (0 upto length sets - 1)
  end;


(* Define new MRBNFs *)

fun check_bd_termT bd_term =
  if (bd_term |> fastype_of |> Term.add_tfreesT) [] |> null then bd_term
  else error "Can't have type variables in the type of the bound!";

fun var_assumpt_terms bd_term =
  let
    fun mk_assumption name term = ((Binding.name name, []), single (term, []));
    val large = HOLogic.mk_UNIV undefT
      |> mk_card_of
      |> mk_ordLeq bd_term
      |> HOLogic.mk_Trueprop
      |> mk_assumption var_type_class_ass1N;
    val regular = HOLogic.mk_UNIV undefT
      |> mk_card_of
      |> mk_regularCard
      |> HOLogic.mk_Trueprop
      |> mk_assumption var_type_class_ass2N;
  in
    Element.Assumes [large, regular]
  end;

fun get_class_assumption class assN lthy =
  let
    val local_class = null class;
    val thmN = if local_class then assN else short_type_name (the_single class) ^ "_class." ^ assN;
    val (context, facts) = (if local_class then `Context.Proof else Proof_Context.theory_of #>
      `Context.Theory ##> Proof_Context.init_global) lthy ||> Proof_Context.facts_of;
  in
    Facts.intern facts thmN
      |> Facts.lookup context facts
      |> the
      |> #thms
      |> the_single
      |> Thm.transfer' lthy
  end;
val get_local_class_assumption = get_class_assumption [];

fun prove_instantiation name class tac = Class.instantiation ([name], [], class)
  #> Class.prove_instantiation_exit tac |> Local_Theory.background_theory;

fun as_subclass_of super_class subclass_tac ctxt =
  Class_Declaration.prove_subclass (subclass_tac ctxt) (the_single super_class) ctxt;

fun define_var_type_class var_binding bd_term =
  Local_Theory.background_theory_result (
    Class_Declaration.class var_binding [] [] [
      check_bd_termT bd_term |> mk_Field |> mk_card_of |> var_assumpt_terms
    ] #> apfst single #> apsnd Local_Theory.exit_global
  )

fun define_covar_type_class bd_term var_binding class subclass_tac =
  Class_Declaration.class var_binding [] [] [check_bd_termT bd_term |> BNF_LFP_Util.mk_cardSuc
    |> var_assumpt_terms] #>> single ##> as_subclass_of class subclass_tac
  ##> Local_Theory.exit_global |> Local_Theory.background_theory_result;

val is_live = curry (op =) Live_Var;
val is_bound = curry (op =) Bound_Var;
val is_free = curry (op =) Free_Var;

fun map_var_types (var_types : var_type list) map x y = map (fn Live_Var => x | _ => y) var_types;

fun mk_TFree_betas var_types get_alphas x lthy =
  let
    val live = count is_live var_types
    val (lives', new_lthy) = mk_TFrees live lthy
    fun map_fun Live_Var _ (T :: Ts) = (T, Ts)
      | map_fun _ T Ts = (T, Ts)
  in
    ((x, @{fold_map 2} map_fun var_types (get_alphas x) lives' |> fst), new_lthy)
  end;

fun mk_ordLess t1 t2 = HOLogic.mk_mem (HOLogic.mk_prod (t1, t2),
  Const (@{const_name ordLess}, mk_relT (fastype_of t1, fastype_of t2)));

val (add_prems, add_map_transfer_prems, mk_prem_terms) =
  let
    fun test_TEqu (T1 : typ, T2 : typ) = if T1 = T2 then (T1, T2) else error "Types must be equal";

    fun mk_small_support t = t
      |> fastype_of
      |> dest_funT
      |> test_TEqu
      |> fst
      |> HOLogic.mk_UNIV
      |> mk_card_of
      |> mk_ordLess (MRBNF_Util.mk_supp t |> mk_card_of);
    val mk_small_support_imp = mk_small_support #> HOLogic.mk_Trueprop #> curry Logic.mk_implies;

    fun mk_bij t = t
      |> fastype_of
      |> dest_funT
      |> test_TEqu
      |> apply2 HOLogic.mk_UNIV
      |-> BNF_LFP_Util.mk_bij_betw t;
    val mk_bij_imp = mk_bij #> HOLogic.mk_Trueprop #> curry Logic.mk_implies;
    fun mk_prem t = mk_small_support t
      |> curry HOLogic.mk_conj (mk_bij t);

    fun map_fun (var_type, t) prop = case var_type of
      Live_Var => prop
      | Bound_Var => mk_small_support_imp t prop |> mk_bij_imp t
      | Free_Var => mk_small_support_imp t prop;

    fun eq_onp_of f = `f #> swap #-> lambda #> mk_eq_onp;

    fun rel_map_fun (var_type, t) = case var_type of
      Live_Var => mk_rel_fun t
      | Bound_Var => eq_onp_of mk_prem t |> mk_rel_fun
      | Free_Var => eq_onp_of mk_small_support t |> mk_rel_fun;

    fun mk_fun_map var_type t = case var_type of
      Live_Var => []
      | Bound_Var => [mk_bij t, mk_small_support t] |> map (HOLogic.mk_Trueprop)
      | Free_Var => [mk_small_support t |> HOLogic.mk_Trueprop];
  in
    (fold_rev map_fun oo map2 pair,
    fold_rev rel_map_fun oo map2 pair,
    flat oo map2 mk_fun_map)
  end;

fun define_mrbnf_consts const_policy fact_policy internal Ds_opt classes_opt map_b rel_b pred_b set_bs
    ((((((((mrbnf_b, T_rhs), map_rhs), var_set_rhss), bd_rhs), wit_rhss), rel_rhs_opt),
    pred_rhs_opt), sort_opt) no_defs_lthy =
  let
    val (var_types, set_rhss) = split_list var_set_rhss;
    val non_dead = length var_types;
    val live = count is_live var_types;
    fun filter_lives xs = filter_like var_types is_live xs;

    fun subs_VT x = map_var_types var_types map x;
    fun map_VT f = map_var_types var_types map2 f;
    fun zip_map_VT f g = map_VT f g oo (curry op ~~);
    fun fold_map_VT f = map_var_types var_types (fn f => fold_map (uncurry f) oo map2 pair) f;
    fun map2_VT f = map_var_types var_types @{map 3} f;

    val def_qualify = Binding.qualify false (Binding.name_of mrbnf_b);

    fun mk_prefix_binding pre = Binding.prefix_name (pre ^ "_") mrbnf_b;

    fun maybe_define user_specified (b, rhs) lthy =
      let
        val inline =
          (user_specified orelse fact_policy = Dont_Note) andalso
          (case const_policy of
            Dont_Inline => false
          | Hardly_Inline => Term.is_Free rhs orelse Term.is_Const rhs
          | Smart_Inline => Term.size_of_term rhs <= smart_max_inline_term_size
          | Do_Inline => true);
      in
        if inline then
          ((rhs, Drule.reflexive_thm), lthy)
        else
          let val b = b () in
            apfst (apsnd snd)
              ((if internal then Local_Theory.define_internal else Local_Theory.define)
                ((b, NoSyn), ((Binding.concealed (Thm.def_binding b), []), rhs)) lthy)
          end
      end;

    val map_bind_def =
      (fn () => def_qualify (if Binding.is_empty map_b then mk_prefix_binding mapN else map_b),
         map_rhs);
    val set_binds_defs =
      let
        fun set_name i get_b =
          (case try (nth set_bs) (i - 1) of
            SOME b => if Binding.is_empty b then get_b else K b
          | NONE => get_b) #> def_qualify;
        val bs = if non_dead = 1 then [set_name 1 (fn () => mk_prefix_binding setN)]
          else map (fn i => set_name i (fn () => mk_prefix_binding (mk_setN i))) (1 upto non_dead);
      in bs ~~ set_rhss end;
    val bd_bind_def = (fn () => def_qualify (mk_prefix_binding bdN), bd_rhs);

    val (((mrbnf_map_term, raw_map_def),
      (mrbnf_set_terms, raw_set_defs)),
      (lthy, lthy_old)) =
        no_defs_lthy
        |> Local_Theory.begin_nested |> snd
        |> maybe_define true map_bind_def
        ||>> apfst split_list o fold_map (maybe_define true) set_binds_defs
        ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val ((mrbnf_bd_term, raw_bd_def), (lthy, lthy_old)) = snd (Local_Theory.begin_nested lthy)
      |> maybe_define true bd_bind_def
      ||> `Local_Theory.end_nested;

    val phi' = Proof_Context.export_morphism lthy_old lthy;
    val mrbnf_bd_def = Morphism.thm phi' raw_bd_def;

    val mrbnf_map_def = Morphism.thm phi raw_map_def;
    val mrbnf_set_defs = map (Morphism.thm phi) raw_set_defs;
    (*val mrbnf_bd_def = Morphism.thm phi raw_bd_def;*)

    val mrbnf_map_raw = Morphism.term phi mrbnf_map_term;

    (*TODO: handle errors*)
    (*simple shape analysis of a map function*)
    val ((alphas_raw, betas_raw), (Calpha_raw, _)) =
      fastype_of mrbnf_map_raw
      |> strip_typeN non_dead
      |>> map_split dest_funT
      ||> dest_funT
      handle TYPE _ => error "Bad map function";

    val Calpha_params_raw = map TVar (Term.add_tvarsT Calpha_raw []);

    val mrbnf_T = Morphism.typ phi T_rhs;
    val bad_args = Term.add_tfreesT mrbnf_T [];
    val _ = null bad_args orelse error ("Locally fixed type arguments " ^
      commas_quote (map (Syntax.string_of_typ no_defs_lthy o TFree) bad_args));

    fun mk_mrbnf_bd Calpha_params =
      Term.subst_TVars (Term.add_tvar_namesT mrbnf_T [] ~~ Calpha_params)
        (Morphism.term phi' mrbnf_bd_term);
    val mrbnf_bd_raw =  mk_mrbnf_bd Calpha_params_raw;

    fun unfold_bd_def' lthy = Local_Defs.unfold0 lthy (
      (map (fn thm => @{thm symmetric} OF [thm]) (no_reflexive [mrbnf_bd_def]))
    );
    val unfold_bd_def = unfold_bd_def' lthy;
    val ((class, var_large, var_regular), (mk_covar_type_class, mk_covar_large), lthy) = case classes_opt of
        SOME ((class, var_large, var_regular), (coclass, mk_covar_large)) =>
          ((class, unfold_bd_def var_large, var_regular), (K (pair coclass), fn (sort, lthy) => unfold_bd_def' lthy (mk_covar_large (sort, lthy))), lthy)
      | NONE => case mrbnf_bd_raw of
        Const (@{const_name natLeq}, _) =>
          ((@{sort var}, @{thm var_class.large}, @{thm var_class.regular}), (K (pair @{sort covar}), K @{thm covar_class.large}), lthy)
        | _ =>
        let
          val (class, lthy) = case sort_opt of
            SOME class => (class, lthy)
            | NONE => define_var_type_class (mk_prefix_binding var_typeN) mrbnf_bd_raw lthy;
          val var_large = get_class_assumption class var_type_class_ass1N lthy
          val var_regular = get_class_assumption class var_type_class_ass2N lthy
          val mk_covar_large = fn (coclass, lthy) => get_class_assumption coclass var_type_class_ass1N lthy

          val ((wit_covar_name, wit_covar_def), lthy) =
            let
              val term = mk_csum (mk_Field mrbnf_bd_raw
                |> mk_card_of) @{term natLeq} |> BNF_LFP_Util.mk_cardSuc |> mk_Field;
            in
              new_typedef (mk_prefix_binding covar_witN) term mk_mr_typedef_tac lthy
                |>> apsnd (snd #> #type_definition)
            end;
          val lthy = prove_instantiation wit_covar_name class
            (mk_mr_instance_proof_tac wit_covar_def NONE) lthy;

          fun mk_covar_type_class bd_Card_order lthy =
            let
              fun subclass_tac ctxt =
                let
                  val colarge = get_local_class_assumption var_type_class_ass1N ctxt;
                  val coregular = get_local_class_assumption var_type_class_ass2N ctxt;
                in
                  mk_mr_subclass_tac ctxt bd_Card_order colarge coregular
                end;
              val (coclass, lthy) = define_covar_type_class mrbnf_bd_raw
                (mk_prefix_binding covar_typeN) class subclass_tac lthy;
              val lthy = prove_instantiation wit_covar_name coclass
                (mk_mr_instance_proof_tac wit_covar_def (SOME bd_Card_order)) lthy;
            in (coclass, lthy) end;
        in
          ((class, var_large, var_regular), (mk_covar_type_class, mk_covar_large), lthy)
        end;

    val (alphas, betas, deads, Calpha, Calpha_params, mrbnf_map) =
      let
        fun fold_fun f T lthy = case T of
          Type (s, Ts) => fold_map (fold_fun f) Ts lthy |>> Type o pair s
          | TFree (_, S) => yield_singleton mk_TFrees' (f S) lthy
          | TVar ((_, i), S) => yield_singleton Variable.invent_types (f S) lthy
            |>> TVar o apfst (rpair i);
        val (alphas', (betas', lthy')) = fold_map_VT (fold_fun I) (K class |> fold_fun) alphas_raw lthy
          ||> fold_map_VT (fold_fun I) pair betas_raw
        val (betas, alphas) = (alphas', betas')
          ||> zip_map_VT fst snd |> `op |>
          ||> fst;

        val mrbnf_map' = subst_atomic_types (alphas_raw @ betas_raw ~~ alphas @ betas) mrbnf_map_raw;

        (*TODO: assert Ds = (TVars of mrbnf_map) \ (alphas' @ betas') as sets*)
        val (deads_raw, deads) = (case Ds_opt of
          NONE => let val Ds = subtract (op =) (alphas @ betas) (map TVar (Term.add_tvars mrbnf_map' []))
                  in (Ds, Ds) end
        | SOME Ds => let val Ds' = map (Morphism.typ phi) Ds
                     in (Ds', fst (fold_map (fold_fun I) Ds' lthy')) end);
        val map_fun = typ_subst_atomic (alphas_raw @ betas_raw @ deads_raw ~~ alphas @ betas @ deads);
        val mrbnf_map = subst_atomic_types (alphas_raw @ betas_raw @ deads_raw ~~ alphas @ betas @ deads) mrbnf_map_raw;
      in
        (alphas, betas, deads, map_fun Calpha_raw, map map_fun Calpha_params_raw, mrbnf_map)
      end;

    val mrbnf_sets =
      map2 (normalize_set Calpha_params) alphas (map (Morphism.term phi) mrbnf_set_terms);
    val mrbnf_bd = mk_mrbnf_bd Calpha_params;

    (*TODO: further checks of type of mrbnf_map*)
    (*TODO: check types of mrbnf_sets*)
    (*TODO: check type of mrbnf_bd*)
    (*TODO: check type of mrbnf_rel*)

    fun mk_mrbnf_map Ds As' Bs' =
      Term.subst_atomic_types ((deads ~~ Ds) @ (alphas ~~ As') @ (betas ~~ Bs')) mrbnf_map;
    fun mk_mrbnf_t Ds As' = Term.subst_atomic_types ((deads ~~ Ds) @ (alphas ~~ As'));
    fun mk_mrbnf_T Ds As' = Term.typ_subst_atomic ((deads ~~ Ds) @ (alphas ~~ As'));

    val (((As, Bs), unsorted_Ds), names_lthy) = lthy
      |> mk_TFrees' (subs_VT @{sort type} class)
      |-> mk_TFree_betas var_types I
      ||>> mk_TFrees (length deads);

    val Ds = map2 (resort_tfree_or_tvar o Type.sort_of_atyp) deads unsorted_Ds;
    val (lAs, lBs) = apply2 filter_lives (As, Bs);
    val mrbnf_lsets = filter_lives mrbnf_sets;

    val RTs = zip_map_VT HOLogic.mk_prodT fst As Bs;
    val pred2RTs = map2 mk_pred2T lAs lBs;
    val (Rs, Rs') = names_lthy |> mk_Frees' "R" pred2RTs |> fst;
    val CA = mk_mrbnf_T Ds As Calpha;
    val CR = mk_mrbnf_T Ds RTs Calpha;
    val setRs =
      @{map 3} (fn R => fn T => fn U =>
          HOLogic.Collect_const (HOLogic.mk_prodT (T, U)) $ HOLogic.mk_case_prod R) Rs lAs lBs;

    (*Grp (in (Collect (split R1) .. Collect (split Rn))) (map fst .. fst)^--1 OO
      Grp (in (Collect (split R1) .. Collect (split Rn))) (map snd .. snd)*)
    fun rel_spec fs =
      let
        val map1 = Term.list_comb (mk_mrbnf_map Ds RTs As, map_VT fst_const HOLogic.id_const RTs);
        val map2 = Term.list_comb (mk_mrbnf_map Ds RTs Bs, map2_VT (K snd_const) K fs RTs);
        val mrbnf_in = mk_in setRs (map (mk_mrbnf_t Ds RTs) mrbnf_lsets) CR;
      in
        mk_rel_compp (mk_conversep (mk_Grp mrbnf_in map1), mk_Grp mrbnf_in map2)
        |> fold_rev Term.absfree Rs'
      end;

    val rel_rhs = the_default (map HOLogic.id_const RTs |> rel_spec) rel_rhs_opt;

    val rel_bind_def =
      (fn () => def_qualify (if Binding.is_empty rel_b then mk_prefix_binding relN else rel_b),
         rel_rhs);

    val pred_spec =
      if live = 0 then Term.absdummy (mk_mrbnf_T Ds As Calpha) @{term True} else
      let
        val sets = map (mk_mrbnf_t Ds As) mrbnf_lsets;
        val argTs = map mk_pred1T lAs;
        val T = mk_mrbnf_T Ds As Calpha;
        val ((Ps, Ps'), x) = lthy
          |> mk_Frees' "P" argTs
          ||>> yield_singleton (mk_Frees "x") T
          |> fst;
        val conjs = map2 (fn set => fn P => mk_Ball (set $ x) P) sets Ps;
      in
        fold_rev Term.absfree Ps'
          (Term.absfree (dest_Free x) (Library.foldr1 HOLogic.mk_conj conjs))
      end;

    val pred_rhs = the_default pred_spec pred_rhs_opt;

    val pred_bind_def =
      (fn () => def_qualify (if Binding.is_empty pred_b then mk_prefix_binding predN else pred_b),
         pred_rhs);

    val wit_rhss =
      if null wit_rhss then
        let
          fun fold_fun var_type T (t, i) = case var_type of
            Live_Var => (t $ Term.absdummy T (Bound i), i-1)
            | _=> (t $ HOLogic.id_const T, i);
        in
          [fst (fold2 fold_fun var_types As (mk_mrbnf_map Ds As As, live)) $
            Const (@{const_name undefined}, CA) |> fold_rev Term.absdummy lAs]
        end
      else wit_rhss;
    val nwits = length wit_rhss;
    val wit_binds_defs =
      let
        val bs = if nwits = 1 then [fn () => def_qualify (mk_prefix_binding witN)]
          else map (fn i => fn () => def_qualify (mk_prefix_binding (mk_witN i))) (1 upto nwits);
      in bs ~~ wit_rhss end;

    val ((((mrbnf_rel_term, raw_rel_def), (mrbnf_pred_term, raw_pred_def)),
        (mrbnf_wit_terms, raw_wit_defs)), (lthy, lthy_old)) =
      lthy
      |> Local_Theory.begin_nested |> snd
      |> maybe_define (is_some rel_rhs_opt) rel_bind_def
      ||>> maybe_define (is_some pred_rhs_opt) pred_bind_def
      ||>> apfst split_list o fold_map (maybe_define (not (null wit_rhss))) wit_binds_defs
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val mrbnf_rel_def = Morphism.thm phi raw_rel_def;
    val mrbnf_rel = Morphism.term phi mrbnf_rel_term;
    fun mk_mrbnf_rel Ds (As', lAs') (Bs', lBs') =
      normalize_rel lthy (map2 mk_pred2T lAs' lBs') (mk_mrbnf_T Ds As' Calpha)
        (mk_mrbnf_T Ds Bs' Calpha) mrbnf_rel;

    val mrbnf_pred_def = Morphism.thm phi raw_pred_def;
    val mrbnf_pred = Morphism.term phi mrbnf_pred_term;
    fun mk_mrbnf_pred Ds (As', lAs') =
      normalize_pred lthy (map mk_pred1T lAs') (mk_mrbnf_T Ds As' Calpha) mrbnf_pred;

    val mrbnf_wit_defs = map (Morphism.thm phi) raw_wit_defs;
    val mrbnf_wits = map (normalize_wit
      Calpha_params Calpha (filter_lives alphas) o Morphism.term phi) mrbnf_wit_terms;

    fun mk_rel_spec Ds' fs =
      let
        val (As', Bs') = map_split (dest_funT o fastype_of) fs;
      in
        Term.subst_atomic_types ((Ds ~~ Ds') @ (As ~~ As') @ (Bs ~~ Bs')) (rel_spec fs)
      end;

    fun mk_pred_spec Ds' As' =
      Term.subst_atomic_types ((Ds ~~ Ds') @ (As ~~ As')) pred_spec;
  in
    (((alphas, betas, deads, Calpha, (class, var_large, var_regular), (mk_covar_type_class, mk_covar_large)),
     (mrbnf_map, mrbnf_sets, mrbnf_bd, mrbnf_wits, mrbnf_rel, mrbnf_pred),
     (mrbnf_map_def, mrbnf_set_defs, mrbnf_bd_def, mrbnf_wit_defs, mrbnf_rel_def, mrbnf_pred_def),
     (mk_mrbnf_map, mk_mrbnf_t, mk_mrbnf_T, mk_mrbnf_rel, mk_mrbnf_pred, mk_rel_spec,
       mk_pred_spec)), lthy)
  end;

fun prepare_def const_policy mk_fact_policy internal qualify prep_typ prep_term prep_sort Ds_opt classes_opt
  map_b rel_b pred_b set_bs ((((((((raw_mrbnf_b, raw_mrbnf_T), raw_map), raw_var_sets), raw_bd),
    raw_wits), raw_rel_opt), raw_pred_opt), raw_sort_opt) no_defs_lthy =
  let
    val fact_policy = mk_fact_policy no_defs_lthy;
    val mrbnf_b = qualify raw_mrbnf_b;
    val (var_types, raw_sets) = split_list raw_var_sets;
    val non_dead = length var_types;
    fun filter_frees xs = filter_like var_types is_free xs;
    fun filter_bounds xs = filter_like var_types is_bound xs;
    fun filter_lives xs = filter_like var_types is_live xs;
    fun filter_non_lives xs = filter_like var_types (not o is_live) xs;

    fun subs_VT x = map_var_types var_types map x;
    fun map_VT f = map_var_types var_types map2 f;
    fun map2_VT f = map_var_types var_types @{map 3} f;
    fun zip_map_VT f g = map_VT f g oo (curry op ~~);
    fun fold_map_VT f = map_var_types var_types (fn f => fold_map (uncurry f) oo map2 pair) f;
    fun comb_frels fs Rs = fold_map_VT (K dest_cons) pair fs Rs |> fst;

    val T_rhs = prep_typ no_defs_lthy raw_mrbnf_T;
    val map_rhs = prep_term no_defs_lthy raw_map;
    val set_rhss = map (prep_term no_defs_lthy) raw_sets;
    val bd_rhs = prep_term no_defs_lthy raw_bd;
    val wit_rhss = map (prep_term no_defs_lthy) raw_wits;
    val rel_rhs_opt = Option.map (prep_term no_defs_lthy) raw_rel_opt;
    val pred_rhs_opt = Option.map (prep_term no_defs_lthy) raw_pred_opt;
    val sort_opt = Option.map (prep_sort no_defs_lthy) raw_sort_opt;

    fun err T =
      error ("Trying to register the type " ^ quote (Syntax.string_of_typ no_defs_lthy T) ^
        " as unnamed MRBNF");

    val (mrbnf_b, key) =
      if Binding.is_empty mrbnf_b then
        (case T_rhs of
          Type (C, Ts) =>
          if forall (can dest_TFree) Ts andalso not (has_duplicates (op =) Ts) then
            (Binding.qualified_name C, C)
          else
            err T_rhs
        | T => err T)
      else
        (mrbnf_b, Local_Theory.full_name no_defs_lthy mrbnf_b);

    val (((alphas, betas, deads, Calpha, (class, var_large_raw, var_regular), (mk_covar_type_class, mk_covar_large)),
     (mrbnf_map, mrbnf_sets, mrbnf_bd, mrbnf_wits, mrbnf_rel, mrbnf_pred),
     (mrbnf_map_def, mrbnf_set_defs, mrbnf_bd_def, mrbnf_wit_defs, mrbnf_rel_def, mrbnf_pred_def),
     (mk_mrbnf_map_Ds, mk_mrbnf_t_Ds, mk_mrbnf_T_Ds, _, _, mk_rel_spec, mk_pred_spec)), lthy) =
       define_mrbnf_consts const_policy fact_policy internal Ds_opt classes_opt map_b rel_b pred_b set_bs
         ((((((((mrbnf_b, T_rhs), map_rhs), (var_types ~~ set_rhss)), bd_rhs), wit_rhss), rel_rhs_opt),
           pred_rhs_opt), sort_opt) no_defs_lthy;

    val dead = length deads;

    val (((((((As', Bs'), Cs), unsorted_Ds), Es), B1Ts), B2Ts), (Ts, T)) = lthy
      |> mk_TFrees' (subs_VT @{sort type} class)
      |-> mk_TFree_betas var_types I
      |-> mk_TFree_betas var_types snd
      ||>> mk_TFrees dead
      |-> mk_TFree_betas var_types (snd o fst)
      |-> mk_TFree_betas var_types snd
      |-> mk_TFree_betas var_types snd
      ||> fst o mk_TFrees' [class]
      ||> the_single
      ||> `(replicate non_dead);

    val Ds = map2 (resort_tfree_or_tvar o Type.sort_of_atyp) deads unsorted_Ds;
    val Ts' = map_VT I (K T) As';
    val (lAs', lBs', lCs, lEs, lB1Ts, lB2Ts) = @{apply 6} filter_lives
      (As', Bs', Cs, Es, B1Ts, B2Ts);

    val mk_mrbnf_prems = add_prems var_types;
    val mk_mrbnf_prem_terms = mk_prem_terms var_types;
    val mk_mrbnf_map = mk_mrbnf_map_Ds Ds;
    val mk_mrbnf_t = mk_mrbnf_t_Ds Ds;
    val mk_mrbnf_T = mk_mrbnf_T_Ds Ds;

    val pred1PTs = map mk_pred1T lAs';
    val pred1QTs = map mk_pred1T lBs';
    val pred2RTs = map2 mk_pred2T lAs' lBs';
    val pred2RTsAsCs = map2 mk_pred2T lAs' lCs;
    val pred2RTsBsCs = map2 mk_pred2T lBs' lCs;
    val pred2RTsBsEs = map2 mk_pred2T lBs' lEs;
    val pred2RTsCsBs = map2 mk_pred2T lCs lBs';
    val pred2RTsCsEs = map2 mk_pred2T lCs lEs;
    val pred2RT's = map2 mk_pred2T lBs' lAs';
    val self_pred2RTs = map2 mk_pred2T lAs' lAs';
    val transfer_domRTs = map2 mk_pred2T lAs' lB1Ts;
    val transfer_ranRTs = map2 mk_pred2T lBs' lB2Ts;

    val CA' = mk_mrbnf_T As' Calpha;
    val CB' = mk_mrbnf_T Bs' Calpha;
    val CC' = mk_mrbnf_T Cs Calpha;
    val CE' = mk_mrbnf_T Es Calpha;
    val CB1 = mk_mrbnf_T B1Ts Calpha;
    val CB2 = mk_mrbnf_T B2Ts Calpha;

    val mrbnf_map_AsAs = mk_mrbnf_map As' As';
    val mrbnf_map_AsBs = mk_mrbnf_map As' Bs';
    val mrbnf_map_AsCs = mk_mrbnf_map As' Cs;
    val mrbnf_map_BsCs = mk_mrbnf_map Bs' Cs;
    val mrbnf_sets_As = map (mk_mrbnf_t As') mrbnf_sets;
    val mrbnf_sets_Bs = map (mk_mrbnf_t Bs') mrbnf_sets;
    val mrbnf_sets_Ts = map (mk_mrbnf_t Ts') mrbnf_sets;
    val mrbnf_bd_As = mk_mrbnf_t As' mrbnf_bd;
    fun mk_mrbnf_rel RTs CA CB = normalize_rel lthy RTs CA CB mrbnf_rel;
    fun mk_mrbnf_pred PTs CA = normalize_pred lthy PTs CA mrbnf_pred;

    val (((((((((((((((((((((((((((fs, fs'), gs), hs), is), x), x'), y), y'), z), zs), zs'), ys),
      As), As_copy), bs), (Ps, Ps')), Ps_copy), Qs), Rs), Rs_copy), Ss), S_AsCs), S_CsBs), S_BsEs),
      transfer_domRs), transfer_ranRs), frees_lthy) = lthy
      |> mk_Frees "f" (map2 (curry op -->) As' Bs')
      ||>> mk_Frees "f" (map2 (curry op -->) As' Bs')
      ||>> mk_Frees "g" (map2 (curry op -->) Bs' Cs)
      ||>> mk_Frees "h" (map2 (curry op -->) Ts' Ts)
      ||>> mk_Frees "i" (map2 (curry op -->) As' Cs)
      ||>> yield_singleton (mk_Frees "x") CA'
      ||>> yield_singleton (mk_Frees "x") CA'
      ||>> yield_singleton (mk_Frees "y") CB'
      ||>> yield_singleton (mk_Frees "y") CB'
      ||>> yield_singleton (mk_Frees "z") CC'
      ||>> mk_Frees "z" As'
      ||>> mk_Frees "z" As'
      ||>> mk_Frees "y" Bs'
      ||>> mk_Frees "A" (map HOLogic.mk_setT As')
      ||>> mk_Frees "A" (map HOLogic.mk_setT As')
      ||>> mk_Frees "b" As'
      ||>> mk_Frees' "P" pred1PTs
      ||>> mk_Frees "P" pred1PTs
      ||>> mk_Frees "Q" pred1QTs
      ||>> mk_Frees "R" pred2RTs
      ||>> mk_Frees "R" pred2RTs
      ||>> mk_Frees "S" pred2RTsBsCs
      ||>> mk_Frees "S" pred2RTsAsCs
      ||>> mk_Frees "S" pred2RTsCsBs
      ||>> mk_Frees "S" pred2RTsBsEs
      ||>> mk_Frees "R" transfer_domRTs
      ||>> mk_Frees "S" transfer_ranRTs;

    val fs_copy = map2 (retype_const_or_free o fastype_of) fs gs;
    val x_copy = retype_const_or_free CA' y';
    val y_copy = retype_const_or_free CB' x';
    val (lfs, lfs', lfs_copy, lgs, lis, lzs, lzs', lys,
      lAs, lAs_copy, lbs, mrbnf_sets_lAs, mrbnf_sets_lBs) = @{apply 13} filter_lives
      (fs, fs', fs_copy, gs, is, zs, zs', ys, As, As_copy, bs, mrbnf_sets_As, mrbnf_sets_Bs);
    val (lfs_id, lfs'_id, lgs_id, lis_id) = @{apply 4}
      (map2_VT K (K HOLogic.id_const) |> uncurry)
      ((fs, As'), (fs', As'), (gs, As'), (is, As'));

    val prems_fs = mk_mrbnf_prems fs;
    val prems_fsfs_copy = prems_fs o mk_mrbnf_prems fs_copy;
    val prems_fsgs = prems_fs o mk_mrbnf_prems gs;
    val prems_hs = mk_mrbnf_prems hs;

    val rel = mk_mrbnf_rel pred2RTs CA' CB';
    val pred = mk_mrbnf_pred pred1PTs CA';
    val pred' = mk_mrbnf_pred pred1QTs CB';
    val relCsEs = mk_mrbnf_rel pred2RTsCsEs CC' CE';
    val relAsAs = mk_mrbnf_rel self_pred2RTs CA' CA';
    val mrbnf_wit_As = map (apsnd (mk_mrbnf_t As')) mrbnf_wits;

    val map_id0_goal =
      let val mrbnf_map_app_id = Term.list_comb (mrbnf_map_AsAs, map HOLogic.id_const As') in
        mk_Trueprop_eq (mrbnf_map_app_id, HOLogic.id_const CA')
      end;

    val map_comp0_goal =
      let
        val mrbnf_map_app_comp = Term.list_comb
          (mrbnf_map_AsCs, map2 (curry HOLogic.mk_comp) gs fs);
        val comp_mrbnf_map_app = HOLogic.mk_comp
          (Term.list_comb (mrbnf_map_BsCs, gs), Term.list_comb (mrbnf_map_AsBs, fs));
      in
        fold_rev Logic.all (fs @ gs) (mk_Trueprop_eq (mrbnf_map_app_comp, comp_mrbnf_map_app)
          |> prems_fsgs)
      end;

    fun mk_map_cong_prem mk_implies x z set f f_copy =
      Logic.all z (mk_implies (mk_Trueprop_mem (z, set $ x), mk_Trueprop_eq (f $ z, f_copy $ z)));

    val map_cong0_goal =
      let
        val prems = @{map 4} (mk_map_cong_prem Logic.mk_implies x) zs mrbnf_sets_As fs fs_copy;
        val eq = mk_Trueprop_eq (Term.list_comb (mrbnf_map_AsBs, fs) $ x,
          Term.list_comb (mrbnf_map_AsBs, fs_copy) $ x);
      in
        fold_rev Logic.all (x :: fs @ fs_copy) (Logic.list_implies (prems, eq) |> prems_fsfs_copy)
      end;

    val set_map0s_goal =
      let
        fun mk_goal setA setB f =
          let
            val set_comp_map = HOLogic.mk_comp (setB, Term.list_comb (mrbnf_map_AsBs, fs));
            val image_comp_set = HOLogic.mk_comp (mk_image f, setA);
          in
            fold_rev Logic.all fs (mk_Trueprop_eq (set_comp_map, image_comp_set) |> prems_fs)
          end;
      in
        @{map 3} mk_goal mrbnf_sets_As mrbnf_sets_Bs fs
      end;

    val infinite_regular_card_order_bd_goal =
      (*fold_rev Logic.all (filter_frees zs @ filter_bounds zs)*) (
      HOLogic.mk_Trueprop (mk_infinite_regular_card_order mrbnf_bd_As)
    );

    val set_bds_goal =
      let
        fun mk_goal set =
          Logic.all x (HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (set $ x)) mrbnf_bd_As));
      in
        map mk_goal mrbnf_sets_As
      end;

    val relAsCs = mk_mrbnf_rel pred2RTsAsCs CA' CC';
    val relBsCs = mk_mrbnf_rel pred2RTsBsCs CB' CC';
    val relCsBs = mk_mrbnf_rel pred2RTsCsBs CC' CB';
    val rel_OO_lhs = Term.list_comb (relAsCs, map2 (curry mk_rel_compp) Rs Ss);
    val rel_OO_rhs = mk_rel_compp (Term.list_comb (rel, Rs), Term.list_comb (relBsCs, Ss));
    val le_rel_OO_goal =
      fold_rev Logic.all (Rs @ Ss) (HOLogic.mk_Trueprop (mk_leq rel_OO_rhs rel_OO_lhs));

    val rel_OO_Grp_goal =
      let
        val map_x = Term.list_comb (mrbnf_map_AsAs, map2_VT (K HOLogic.id_const) K fs As' @ [x]);
        val abs_vars = (filter_non_lives fs @ Rs @ [x, y]);
      in
        fold_rev Logic.all abs_vars (mk_Trueprop_eq (Term.list_comb (rel, Rs @ [map_x, y]),
          Term.list_comb (mk_rel_spec Ds fs, Rs @ [x, y])) |> prems_fs)
      end;

    val pred_set_goal = fold_rev Logic.all Ps (mk_Trueprop_eq (Term.list_comb (pred, Ps),
      Term.list_comb (mk_pred_spec Ds As', Ps)));

    val goals = zip_axioms map_id0_goal map_comp0_goal map_cong0_goal set_map0s_goal
      infinite_regular_card_order_bd_goal set_bds_goal le_rel_OO_goal rel_OO_Grp_goal
      pred_set_goal;

    val mk_wit_goals = mk_wit_goals lbs lzs mrbnf_sets_lAs;
    fun triv_wit_tac ctxt = mk_trivial_wit_tac ctxt mrbnf_wit_defs;

    val wit_goalss =
      (if null raw_wits then SOME triv_wit_tac else NONE, map mk_wit_goals mrbnf_wit_As);

    fun after_qed mk_wit_thms thms lthy =
      let
        val (axioms, nontriv_wit_thms) = apfst (mk_axioms non_dead) (chop (length goals) thms);

        val frees = filter_frees alphas;
        val free = length frees;
        val bounds = filter_bounds alphas;
        val bound = length bounds;
        val lives = filter_lives alphas;
        val lives' = filter_lives betas;
        val live = length lives;
        val num_prems = free + 2 * bound;

        fun prove_sorry name lthy vars prems goal tac =
          Goal.prove_sorry lthy vars prems goal (fn focus => EVERY [
            if Config.get lthy mrbnf_verbose then print_tac (#context focus) name else all_tac,
            tac focus
          ])

        fun mk_prems supp_thm bij_thm =
          let
            fun fold_fun Free_Var thms = supp_thm :: thms
              | fold_fun Bound_Var thms = bij_thm :: supp_thm :: thms
              | fold_fun Live_Var thms = thms
          in
            fold_rev fold_fun var_types []
          end;

        val id_thms = mk_prems @{thm supp_id_bound} @{thm bij_id};
        fun id_prems thm = thm OF id_thms;
        fun bij_id_prems thm = thm OF replicate (bound+free) @{thms bij_id supp_id_bound} |> flat;
        fun simp_comp_thm lthy = id_prems #> id_prems #> unfold_thms lthy [@{thm o_id}];
        fun simp_cong0_prems thm = thm OF subs_VT @{thm _} refl;

        val bd_infinite_regular_card_order = #bd_infinite_regular_card_order axioms;
        val bd_card_order = bd_infinite_regular_card_order RS @{thm infinite_regular_card_order.card_order};
        val bd_cinfinite = bd_infinite_regular_card_order RS @{thm infinite_regular_card_order.cinfinite};
        val bd_regularCard = bd_infinite_regular_card_order RS @{thm infinite_regular_card_order.regularCard};
        val bd_Card_order = bd_infinite_regular_card_order RS @{thm infinite_regular_card_order.Card_order};
        val bd_Cinfinite = bd_infinite_regular_card_order RS @{thm infinite_regular_card_order.Cinfinite};
        val bd_Cnotzero = bd_infinite_regular_card_order RS @{thm infinite_regular_card_order.Cnotzero};
        val (coclass, lthy) = mk_covar_type_class bd_Card_order lthy;

        val var_large =
            @{thm ordIso_ordLeq_trans} OF [@{thm ordIso_symmetric} OF
              [@{thm card_of_Field_ordIso} OF [bd_Card_order]], var_large_raw];

        val covar_large = mk_covar_large (coclass, lthy)

        val natLeq_bound = @{thm ordLeq_ordLess_trans} OF [@{thm natLeq_ordLeq_cinfinite} OF
          [conjI OF [bd_cinfinite, bd_Card_order]]] OF [@{thm ordLess_ordLeq_trans} OF
          [@{thm cardSuc_greater} OF [bd_Card_order], covar_large]];

        val class_thms = {
          var_large = var_large_raw,
          var_regular = var_regular,
          covar_large = covar_large
        };

        val (UNIV_cinfinite, Un_bound, UNION_bound, lthy) = case class of
          @{sort var} => (@{thm var_class.UNIV_cinfinite}, @{thm infinite_class.Un_bound}, @{thm var_class.UN_bound}, lthy)
          | _ =>
          let
            val UNIV_cinfinite =
              let
                val goal = TFree (Name.aT, class)
                  |> HOLogic.mk_UNIV
                  |> mk_card_of
                  |> mk_cinfinite
                  |> HOLogic.mk_Trueprop;
              in
                prove_sorry "UNIV_cinfinite" lthy [] [] goal (fn {context = ctxt, prems = _} =>
                  EVERY1 [rtac ctxt @{thm cinfinite_mono}, rtac ctxt var_large, rtac ctxt conjunct1,
                    rtac ctxt bd_Cinfinite])
                |> Thm.close_derivation \<^here>
              end;

            val Un_bound =
              let
                val (T, Tc) = lthy |> mk_TFrees 1 ||> fst o mk_TFrees' [class] |> apply2 hd;
                val (A1, A2) = mk_Frees "A" (map HOLogic.mk_setT [T, T]) lthy |> dest_cons o fst ||> hd;
                fun mk_card_bound t = Tc
                  |> HOLogic.mk_UNIV
                  |> mk_card_of
                  |> mk_ordLess (mk_card_of t)
                  |> HOLogic.mk_Trueprop;
                val goal = [A1, A2, mk_union (A1, A2)]
                  |> map mk_card_bound
                  |> foldr1 Logic.mk_implies
                  |> fold_rev Logic.all [A1, A2];
              in
                prove_sorry "Un_bound" lthy [] [] goal (fn {context = ctxt, prems = _} =>
                  EVERY1 [rtac ctxt @{thm card_of_Un_ordLess_infinite},
                    rtac ctxt (unfold_thms ctxt @{thms cinfinite_def Field_card_of} UNIV_cinfinite),
                    REPEAT_DETERM_N 2 o assume_tac ctxt])
                |> Thm.close_derivation \<^here>
              end;

            val UNION_bound =
              let
                val ((Ta, Tb), Tc) = lthy
                  |> mk_TFrees 2
                  |>> apsnd hd o dest_cons
                  ||> hd o fst o mk_TFrees' [class];
                val ((I, A), i) = lthy
                  |> yield_singleton (mk_Frees "I") (HOLogic.mk_setT Ta)
                  ||>> yield_singleton (mk_Frees "A") (Ta --> HOLogic.mk_setT Tb)
                  ||> fst o yield_singleton (mk_Frees "i") Ta;
                fun mk_card_bound t = Tc
                  |> HOLogic.mk_UNIV
                  |> mk_card_of
                  |> mk_ordLess (mk_card_of t)
                  |> HOLogic.mk_Trueprop;
                val goal = [mk_card_bound I,
                    (HOLogic.mk_mem (i, I) |> HOLogic.mk_Trueprop, A $ i |> mk_card_bound)
                      |> Logic.mk_implies |> Logic.all i,
                    mk_UNION I (A $ i |> Term.absfree (dest_Free i)) |> mk_card_bound]
                  |> foldr1 Logic.mk_implies
                  |> fold_rev Logic.all [I, A];
                val bound_Card_order = thm_instantiate_terms lthy [SOME (HOLogic.mk_UNIV Tc)]
                  @{thm card_of_Card_order};
              in
                prove_sorry "UN_bound" lthy [] [] goal (fn {context = ctxt, prems = _} =>
                  EVERY1 [rtac ctxt @{thm regularCard_UNION}, rtac ctxt bound_Card_order,
                    rtac ctxt UNIV_cinfinite, rtac ctxt var_regular, assume_tac ctxt,
                    Goal.assume_rule_tac ctxt])
                |> Thm.close_derivation \<^here>
              end;

            val lthy = Local_Theory.background_theory (fn thy =>
              let
                val lthy = Named_Target.init [] (hd coclass) thy;
                val lthy = snd (Local_Theory.notes (map (fn (thmN, thm) => ((Binding.name thmN, []), [([thm], [])])) [
                  ("large", covar_large)
                ]) lthy) handle ERROR _ => lthy;
              in Local_Theory.exit_global lthy end
            ) lthy;
            val lthy = Local_Theory.background_theory (fn thy =>
              let
                val lthy = Named_Target.init [] (hd class) thy;
                val lthy = snd (Local_Theory.notes (map (fn (thmN, thm) => ((Binding.name thmN, []), [([thm], [])])) [
                  ("Un_bound", Un_bound),
                  ("UN_bound", UNION_bound),
                  ("UNIV_cinfinite", UNIV_cinfinite),
                  ("large'", var_large)
                ]) lthy) handle ERROR _ => lthy;
                val lthy = snd (Local_Theory.notes (map (fn (thmN, thm) => ((Binding.name thmN, []), [([thm], [])])) [
                  ("large", var_large_raw),
                  ("regular", var_regular)
                ]) lthy) handle ERROR _ => lthy;
              in Local_Theory.exit_global lthy end
            ) lthy;
          in (UNIV_cinfinite, Un_bound, UNION_bound, lthy) end;

        val supp_the_inv_bound = @{thm supp_the_inv_bound_gen} OF
            [conjI OF [UNIV_cinfinite, @{thm card_of_Card_order}]];
        val supp_comp_bound =
          let
            val Tc = lthy |> fst o mk_TFrees' [class] |> the_single;
            val (f, g) = mk_Frees "f" [Tc --> Tc, Tc --> Tc] lthy |> dest_cons o fst ||> hd;
            val goal = [f, g, HOLogic.mk_comp (g, f)]
              |> mk_prem_terms (replicate 3 Free_Var)
              |> foldr1 Logic.mk_implies
              |> fold_rev Logic.all [f, g];
          in
            prove_sorry "supp_comp_bound" lthy [] [] goal (fn {context = ctxt, prems = _} =>
              EVERY1 [rtac ctxt @{thm ordLeq_ordLess_trans}, rtac ctxt @{thm card_of_mono1},
                rtac ctxt @{thm supp_o}, rtac ctxt Un_bound,
                REPEAT_DETERM_N 2 o assume_tac ctxt])
            |> Thm.close_derivation \<^here>
          end;

        val the_inv_thms = mk_prems (supp_the_inv_bound, 2)
          (@{thm bij_betw_the_inv_into[of _ UNIV UNIV]}, 1);
        val the_inv_o_thms = mk_prems @{thm supp_the_inv_f_o_f_bound} @{thm bij_the_inv_f_o_f};

        fun mk_collect_set_map () =
          let
            val defT = mk_mrbnf_T Ts Calpha --> HOLogic.mk_setT T;
            val collect_map = HOLogic.mk_comp (mk_collect (map (mk_mrbnf_t Ts) mrbnf_sets) defT,
              Term.list_comb (mk_mrbnf_map Ts' Ts, hs));
            val image_collect = mk_collect
              (map2 (fn h => fn set => HOLogic.mk_comp (mk_image h, set)) hs mrbnf_sets_Ts) defT;
            (*collect {set1 ... setm} o map f1 ... fm = collect {f1` o set1 ... fm` o setm}*)
            val goal = fold_rev Logic.all hs (mk_Trueprop_eq (collect_map, image_collect)
              |> prems_hs);
          in
            prove_sorry "collect_set_map" lthy [] [] goal (fn {context = ctxt, prems = _} =>
              mk_mr_collect_set_map_tac ctxt num_prems (#set_map0 axioms))
            |> Thm.close_derivation \<^here>
          end;

        val collect_set_map = Lazy.lazy mk_collect_set_map;

        fun mk_in_mono As As_copy mrbnf_sets_As non_dead () =
          let
            val prems_mono = map2 (HOLogic.mk_Trueprop oo mk_leq) As As_copy;
            val in_mono_goal =
              fold_rev Logic.all (As @ As_copy)
                (Logic.list_implies (prems_mono, HOLogic.mk_Trueprop
                  (mk_leq (mk_in As mrbnf_sets_As CA') (mk_in As_copy mrbnf_sets_As CA'))));
          in
            prove_sorry "in_mono" lthy [] [] in_mono_goal (fn {context = ctxt, prems = _} =>
              mk_in_mono_tac ctxt non_dead)
            |> Thm.close_derivation \<^here>
          end;

        val in_mono = mk_in_mono As As_copy mrbnf_sets_As non_dead |> Lazy.lazy;
        val weak_in_mono = mk_in_mono lAs lAs_copy mrbnf_sets_lAs live |> Lazy.lazy;

        fun mk_in_cong () =
          let
            val prems_cong = map2 (curry mk_Trueprop_eq) As As_copy;
            val in_cong_goal =
              fold_rev Logic.all (As @ As_copy)
                (Logic.list_implies (prems_cong,
                  mk_Trueprop_eq (mk_in As mrbnf_sets_As CA', mk_in As_copy mrbnf_sets_As CA')));
          in
            prove_sorry "in_cong" lthy [] [] in_cong_goal
              (fn {context = ctxt, prems = _} => (TRY o hyp_subst_tac ctxt THEN' rtac ctxt refl) 1)
            |> Thm.close_derivation \<^here>
          end;

        val in_cong = Lazy.lazy mk_in_cong;

        val map_id = Lazy.lazy (fn () => mk_map_id (#map_id0 axioms));
        val map_ident0 = Lazy.lazy (fn () => mk_map_ident lthy (#map_id0 axioms));
        val map_ident = Lazy.lazy (fn () => mk_map_ident lthy (Lazy.force map_id));
        val map_comp = Lazy.lazy (fn () => mk_map_comp (#map_comp0 axioms));

        val map_comp0_id =  axioms |> #map_comp0 |> simp_comp_thm lthy;
        val map_comp_id = Lazy.map (simp_comp_thm lthy) map_comp;
        val map_cong0_id = axioms |> #map_cong0 |> id_prems |> id_prems |> simp_cong0_prems;
        val weak_set_bd = axioms |> #set_bd |> map (rpair @{thm ordLess_imp_ordLeq} #> op RS);

        fun mk_map_cong mk_implies () =
          let
            val prem0 = mk_Trueprop_eq (x, x_copy);
            val prems = @{map 4} (mk_map_cong_prem mk_implies x_copy) zs mrbnf_sets_As fs fs_copy;
            val eq = mk_Trueprop_eq (Term.list_comb (mrbnf_map_AsBs, fs) $ x,
              Term.list_comb (mrbnf_map_AsBs, fs_copy) $ x_copy);
            val goal = fold_rev Logic.all (x :: x_copy :: fs @ fs_copy)
              (Logic.list_implies (prem0 :: prems, eq) |> prems_fsfs_copy);
          in
            prove_sorry "map_cong" lthy [] [] goal (fn {context = ctxt, prems = _} =>
              unfold_thms_tac ctxt @{thms simp_implies_def} THEN
              mk_mr_map_cong_tac ctxt num_prems (#map_cong0 axioms))
            |> Thm.close_derivation \<^here>
          end;

        val map_cong = Lazy.lazy (mk_map_cong Logic.mk_implies);
        val map_cong_simp = Lazy.lazy (mk_map_cong (fn (a, b) => @{term simp_implies} $ a $ b));

        fun mk_inj_map () =
          let
            val prems = map (HOLogic.mk_Trueprop o mk_inj) fs;
            val concl = HOLogic.mk_Trueprop (mk_inj (Term.list_comb (mrbnf_map_AsBs, fs)));
            val goal = fold_rev Logic.all fs (Logic.list_implies (prems, concl) |> prems_fs);
          in
            prove_sorry "inj_map" lthy [] [] goal (fn {context = ctxt, prems = _} =>
              mk_mr_inj_map_tac ctxt non_dead the_inv_thms the_inv_o_thms id_thms
                (Lazy.force map_id) (Lazy.force map_comp) (#map_cong0 axioms) (Lazy.force map_cong))
            |> Thm.close_derivation \<^here>
          end;

        val inj_map = Lazy.lazy mk_inj_map;

        val set_map = map (fn thm => Lazy.lazy (fn () => mk_set_map thm)) (#set_map0 axioms);
        val set_map_id = set_map |> filter_lives |> map (id_prems o Lazy.force);

        val set_bd_UNIV = map_filter (fn (Live_Var, _) => NONE | (_, set_bd) => SOME (Lazy.lazy (fn () =>
          @{thm ordLess_ordLeq_trans[OF _ ordIso_ordLeq_trans[OF
            iffD1[OF Card_order_iff_ordIso_card_of infinite_regular_card_order.Card_order]]
          ]} OF [set_bd, bd_infinite_regular_card_order, #var_large class_thms]
        ))) (var_types ~~ #set_bd axioms);

        val wit_thms =
          if null nontriv_wit_thms then set_map_id |> mk_wit_thms else nontriv_wit_thms;

        fun mk_in_bd () =
          let
            val bdT = fst (dest_relT (fastype_of mrbnf_bd_As));
            val bdTs = map_VT (K bdT) I As';
            val bd_mrbnfT = mk_mrbnf_T bdTs Calpha;
            val surj_imp_ordLeq_inst = (if live = 0 then TrueI else
              let
                val ranTs = map_VT (fn AT => mk_sumT (AT, HOLogic.unitT)) I As';
                val funTs = map (fn T => bdT --> T) (filter_lives ranTs);
                val ran_mrbnfT = mk_mrbnf_T ranTs Calpha;
                val (revTs, Ts) = `rev (bd_mrbnfT :: funTs);
                val cTs = map (SOME o Thm.ctyp_of lthy) [ran_mrbnfT,
                  Library.foldr1 HOLogic.mk_prodT Ts];
                fun fold_fun var_type T (t, i) = case var_type of
                  Live_Var => (t $ Bound i, i-1)
                  | _=> (t $ HOLogic.id_const T, i);
                val tinst = fold (fn T => fn t =>
                  HOLogic.mk_case_prod (Term.absdummy T t)) (tl revTs)
                    (Term.absdummy (hd revTs) (fst (fold2 fold_fun var_types As'
                      (mk_mrbnf_map bdTs ranTs, live-1)) $ Bound live));
                val cts = [NONE, SOME (Thm.cterm_of lthy tinst)];
              in
                Thm.instantiate' cTs cts @{thm surj_imp_ordLeq}
              end);
            val bd = mk_cexp
              (if live = 0 then ctwo
                else mk_csum (Library.foldr1 (uncurry mk_csum) (map mk_card_of lAs)) ctwo)
              (mk_csum mrbnf_bd_As (mk_card_of (HOLogic.mk_UNIV bd_mrbnfT)));
            val in_bd_goal = fold_rev Logic.all lAs
              (HOLogic.mk_Trueprop (mk_ordLeq (mk_card_of (mk_in lAs mrbnf_sets_lAs CA')) bd));
          in
            prove_sorry "in_bd" lthy [] [] in_bd_goal
              (fn {context = ctxt, prems = _} => mk_in_bd_tac ctxt live surj_imp_ordLeq_inst
                (Lazy.force map_comp_id) (Lazy.force map_id) map_cong0_id set_map_id weak_set_bd
                bd_card_order bd_Card_order bd_Cinfinite bd_Cnotzero)
            |> Thm.close_derivation \<^here>
          end;

        val in_bd = Lazy.lazy mk_in_bd;

        val rel_OO_Grp = #rel_OO_Grp axioms;
        val rel_OO_Grp_ids = Lazy.map (fn map_id => (ext RS ext OF
          [id_prems rel_OO_Grp |> unfold_thms lthy [map_id]]) |> single |> no_refl) map_id;
        val rel_OO_Grp_id = Lazy.map (fn map_id =>
          id_prems rel_OO_Grp |> unfold_thms lthy [map_id] |> mk_abs_def2 lthy) map_id;

        fun mk_rel_Grp () =
          let
            val lhs = Term.list_comb (rel, map2 mk_Grp lAs lfs);
            val rhs = mk_Grp (mk_in lAs mrbnf_sets_lAs CA')
              (Term.list_comb (mrbnf_map_AsBs, lfs_id));
            val goal = fold_rev Logic.all (lAs @ lfs) (mk_Trueprop_eq (lhs, rhs));
          in
            prove_sorry "rel_Grp" lthy [] [] goal
              (fn {context = ctxt, prems = _} => mk_rel_Grp_tac ctxt (Lazy.force rel_OO_Grp_ids)
                (#map_id0 axioms) map_cong0_id (Lazy.force map_id) (Lazy.force map_comp_id)
                set_map_id)
            |> Thm.close_derivation \<^here>
          end;

        val rel_Grp = Lazy.lazy mk_rel_Grp;

        fun mk_rel_prems f = map2 (HOLogic.mk_Trueprop oo f) Rs Rs_copy;
        fun mk_rel_concl f = HOLogic.mk_Trueprop
          (f (Term.list_comb (rel, Rs), Term.list_comb (rel, Rs_copy)));

        fun mk_rel_mono () =
          let
            val mono_prems = mk_rel_prems mk_leq;
            val mono_concl = mk_rel_concl (uncurry mk_leq);
          in
            prove_sorry "rel_mono" lthy [] []
              (fold_rev Logic.all (Rs @ Rs_copy) (Logic.list_implies (mono_prems, mono_concl)))
              (fn {context = ctxt, prems = _} =>
                mk_rel_mono_tac ctxt (Lazy.force rel_OO_Grp_ids) (Lazy.force weak_in_mono))
            |> Thm.close_derivation \<^here>
          end;

        fun mk_rel_cong0 () =
          let
            val cong_prems = mk_rel_prems (curry HOLogic.mk_eq);
            val cong_concl = mk_rel_concl HOLogic.mk_eq;
          in
            prove_sorry "rel_cong0" lthy [] []
              (fold_rev Logic.all (Rs @ Rs_copy) (Logic.list_implies (cong_prems, cong_concl)))
              (fn {context = ctxt, prems = _} => (TRY o hyp_subst_tac ctxt THEN' rtac ctxt refl) 1)
            |> Thm.close_derivation \<^here>
          end;

        val rel_mono = Lazy.lazy mk_rel_mono;
        val rel_cong0 = Lazy.lazy mk_rel_cong0;

        fun mk_rel_eq () =
          prove_sorry "rel_eq" lthy [] []
            (mk_Trueprop_eq (Term.list_comb (relAsAs, map HOLogic.eq_const lAs'),
              HOLogic.eq_const CA'))
            (fn {context = ctxt, prems = _} => mk_mr_rel_eq_tac ctxt live (Lazy.force rel_Grp)
              (Lazy.force rel_cong0) (#map_id0 axioms))
          |> Thm.close_derivation \<^here>;

        val rel_eq = Lazy.lazy mk_rel_eq;

        fun mk_rel_conversep () =
          let
            val relBsAs = mk_mrbnf_rel pred2RT's CB' CA';
            val lhs = Term.list_comb (relBsAs, map mk_conversep Rs);
            val rhs = mk_conversep (Term.list_comb (rel, Rs));
            val le_goal = fold_rev Logic.all Rs (HOLogic.mk_Trueprop (mk_leq lhs rhs));
            val le_thm = prove_sorry "rel_conversep_le" lthy [] [] le_goal
              (fn {context = ctxt, prems = _} => mk_rel_conversep_le_tac ctxt
                (Lazy.force rel_OO_Grp_ids) (Lazy.force rel_eq) map_cong0_id
                (Lazy.force map_comp_id) set_map_id)
              |> Thm.close_derivation \<^here>
            val goal = fold_rev Logic.all Rs (mk_Trueprop_eq (lhs, rhs));
          in
            prove_sorry "rel_conversep" lthy [] [] goal
              (fn {context = ctxt, prems = _} =>
                mk_rel_conversep_tac ctxt le_thm (Lazy.force rel_mono))
            |> Thm.close_derivation \<^here>
          end;

        val rel_conversep = Lazy.lazy mk_rel_conversep;

        fun mk_rel_OO () =
          prove_sorry "rel_OO" lthy [] []
            (fold_rev Logic.all (Rs @ Ss) (HOLogic.mk_Trueprop (mk_leq rel_OO_lhs rel_OO_rhs)))
            (fn {context = ctxt, prems = _} => mk_rel_OO_le_tac ctxt (Lazy.force rel_OO_Grp_ids)
              (Lazy.force rel_eq) map_cong0_id (Lazy.force map_comp_id) set_map_id)
          |> Thm.close_derivation \<^here>
          |> (fn thm => @{thm antisym} OF [thm, #le_rel_OO axioms]);

        val rel_OO = Lazy.lazy mk_rel_OO;

        fun mk_in_rel () = trans OF [rel_OO_Grp, @{thm OO_Grp_alt} RS @{thm predicate2_eqD}];

        val in_rel = Lazy.lazy mk_in_rel;
        val in_rel_id = Lazy.lazy
          (fn () => mk_in_rel () |> id_prems |> unfold_thms lthy [Lazy.force map_id]);

        fun mk_rel_flip () =
          unfold_thms lthy @{thms conversep_iff}
            (Lazy.force rel_conversep RS @{thm predicate2_eqD});

        val rel_flip = Lazy.lazy mk_rel_flip;

        fun mk_rel_mono_strong0 () =
          let
            fun mk_prem setA setB R S a b =
              HOLogic.mk_Trueprop
                (mk_Ball (setA $ x) (Term.absfree (dest_Free a)
                  (mk_Ball (setB $ y) (Term.absfree (dest_Free b)
                    (HOLogic.mk_imp (R $ a $ b, S $ a $ b))))));
            val prems = HOLogic.mk_Trueprop (Term.list_comb (rel, Rs) $ x $ y) ::
              @{map 6} mk_prem mrbnf_sets_lAs mrbnf_sets_lBs Rs Rs_copy lzs lys;
            val concl = HOLogic.mk_Trueprop (Term.list_comb (rel, Rs_copy) $ x $ y);
          in
            prove_sorry "rel_mono_strong0" lthy [] []
              (fold_rev Logic.all (x :: y :: Rs @ Rs_copy) (Logic.list_implies (prems, concl)))
              (fn {context = ctxt, prems = _} =>
                let
                  val in_rel = Lazy.force in_rel_id
                in
                  HEADGOAL (
                    dtac ctxt (@{thm iffD1} OF [in_rel]) THEN'
                    rtac ctxt (@{thm iffD2} OF [in_rel])
                  ) THEN
                  mk_rel_mono_strong0_tac ctxt in_rel set_map_id
                end
              )
            |> Thm.close_derivation \<^here>
          end;

        val rel_mono_strong0 = Lazy.lazy mk_rel_mono_strong0;

        val rel_mono_strong = Lazy.map (Object_Logic.rulify lthy) rel_mono_strong0;

        fun mk_rel_cong_prem mk_implies x x' z z' set set' R R_copy =
          Logic.all z (Logic.all z'
            (mk_implies (mk_Trueprop_mem (z, set $ x), mk_implies (mk_Trueprop_mem (z', set' $ x'),
              mk_Trueprop_eq (R $ z $ z', R_copy $ z $ z')))));

        fun mk_rel_cong mk_implies () =
          let
            val prem0 = mk_Trueprop_eq (x, x_copy);
            val prem1 = mk_Trueprop_eq (y, y_copy);
            val prems = @{map 6} (mk_rel_cong_prem mk_implies x_copy y_copy)
              lzs lys mrbnf_sets_lAs mrbnf_sets_lBs Rs Rs_copy;
            val eq = mk_Trueprop_eq (Term.list_comb (rel, Rs) $ x $ y,
              Term.list_comb (rel, Rs_copy) $ x_copy $ y_copy);
          in
            fold (Variable.add_free_names lthy) (eq :: prem0 :: prem1 :: prems) []
            |> (fn vars => prove_sorry "rel_cong" lthy vars (prem0 :: prem1 :: prems) eq
              (fn {context = ctxt, prems} =>
                mk_rel_cong_tac ctxt (chop 2 prems) (Lazy.force rel_mono_strong)))
            |> Thm.close_derivation \<^here>
          end;

        val rel_cong = Lazy.lazy (mk_rel_cong Logic.mk_implies);
        val rel_cong_simp = Lazy.lazy (mk_rel_cong (fn (a, b) => @{term simp_implies} $ a $ b));

        fun mk_pred_prems f = map2 (HOLogic.mk_Trueprop oo f) Ps Ps_copy;
        fun mk_pred_concl f = HOLogic.mk_Trueprop
          (f (Term.list_comb (pred, Ps), Term.list_comb (pred, Ps_copy)));

        fun mk_pred_cong0 () =
          let
            val cong_prems = mk_pred_prems (curry HOLogic.mk_eq);
            val cong_concl = mk_pred_concl HOLogic.mk_eq;
          in
            prove_sorry "pred_cong0" lthy [] []
              (fold_rev Logic.all (Ps @ Ps_copy) (Logic.list_implies (cong_prems, cong_concl)))
              (fn {context = ctxt, prems = _} => (TRY o hyp_subst_tac ctxt THEN' rtac ctxt refl) 1)
            |> Thm.close_derivation \<^here>
          end;

        val pred_cong0 = Lazy.lazy mk_pred_cong0;

        fun mk_rel_eq_onp () =
          let
            val lhs = Term.list_comb (relAsAs, map mk_eq_onp Ps);
            val rhs = mk_eq_onp (Term.list_comb (pred, Ps));
          in
            prove_sorry "rel_eq_onp" lthy (map fst Ps') [] (mk_Trueprop_eq (lhs, rhs))
              (fn {context = ctxt, prems = _} =>
                mk_rel_eq_onp_tac ctxt (#pred_set axioms) (#map_id0 axioms) (Lazy.force rel_Grp))
            |> Thm.close_derivation \<^here>
          end;

        val rel_eq_onp = Lazy.lazy mk_rel_eq_onp;
        val pred_rel = Lazy.map (fn thm => thm RS sym RS @{thm eq_onp_eqD}) rel_eq_onp;

        fun mk_pred_mono_strong0 () =
          let
            fun mk_prem setA P Q a =
              HOLogic.mk_Trueprop
                (mk_Ball (setA $ x) (Term.absfree (dest_Free a) (HOLogic.mk_imp (P $ a, Q $ a))));
            val prems = HOLogic.mk_Trueprop (Term.list_comb (pred, Ps) $ x) ::
              @{map 4} mk_prem mrbnf_sets_lAs Ps Ps_copy lzs;
            val concl = HOLogic.mk_Trueprop (Term.list_comb (pred, Ps_copy) $ x);
          in
            prove_sorry "pred_mono_strong0" lthy [] []
              (fold_rev Logic.all (x :: Ps @ Ps_copy) (Logic.list_implies (prems, concl)))
              (fn {context = ctxt, prems = _} =>
                mk_pred_mono_strong0_tac ctxt (Lazy.force pred_rel) (Lazy.force rel_mono_strong0))
            |> Thm.close_derivation \<^here>
          end;

        val pred_mono_strong0 = Lazy.lazy mk_pred_mono_strong0;

        val pred_mono_strong = Lazy.map (Object_Logic.rulify lthy) pred_mono_strong0;

        fun mk_pred_mono () =
          let
            val mono_prems = mk_pred_prems mk_leq;
            val mono_concl = mk_pred_concl (uncurry mk_leq);
          in
            prove_sorry "pred_mono" lthy [] []
              (fold_rev Logic.all (Ps @ Ps_copy) (Logic.list_implies (mono_prems, mono_concl)))
              (fn {context = ctxt, prems = _} =>
                mk_pred_mono_tac ctxt (Lazy.force rel_eq_onp) (Lazy.force rel_mono))
            |> Thm.close_derivation \<^here>
          end;

        val pred_mono = Lazy.lazy mk_pred_mono;

        fun mk_pred_cong_prem mk_implies x z set P P_copy =
          Logic.all z
            (mk_implies (mk_Trueprop_mem (z, set $ x), mk_Trueprop_eq (P $ z, P_copy $ z)));

        fun mk_pred_cong mk_implies () =
          let
            val prem0 = mk_Trueprop_eq (x, x_copy);
            val prems = @{map 4} (mk_pred_cong_prem mk_implies x_copy) lzs mrbnf_sets_lAs Ps Ps_copy;
            val eq = mk_Trueprop_eq (Term.list_comb (pred, Ps) $ x,
              Term.list_comb (pred, Ps_copy) $ x_copy);
          in
            fold (Variable.add_free_names lthy) (eq :: prem0 :: prems) []
            |> (fn vars => prove_sorry "pred_cong" lthy vars (prem0 :: prems) eq
              (fn {context = ctxt, prems} =>
                mk_rel_cong_tac ctxt (chop 1 prems) (Lazy.force pred_mono_strong)))
            |> Thm.close_derivation \<^here>
          end;

        val pred_cong = Lazy.lazy (mk_pred_cong Logic.mk_implies);
        val pred_cong_simp = Lazy.lazy (mk_pred_cong (fn (a, b) => @{term simp_implies} $ a $ b));

        fun mk_map_cong_pred () =
          let
            val prem0 = mk_Trueprop_eq (x, x_copy);
            fun mk_eq f g z = Term.absfree (dest_Free z) (HOLogic.mk_eq (f $ z, g $ z));
            val prem = HOLogic.mk_Trueprop
              (Term.list_comb (pred, @{map 3} mk_eq lfs lfs_copy lzs) $ x_copy);
            val eq = mk_Trueprop_eq (Term.list_comb (mrbnf_map_AsBs, fs) $ x,
              Term.list_comb (mrbnf_map_AsBs, map2_VT K (K I) fs_copy fs) $ x_copy);
            val goal = fold_rev Logic.all (x :: x_copy :: fs @ lfs_copy)
              (Logic.list_implies ([prem0, prem], eq) |> prems_fs);
          in
            prove_sorry "map_cong_pred" lthy [] [] goal (fn {context = ctxt, prems = _} =>
              ([unfold_thms_tac ctxt [#pred_set axioms] |> K, REPEAT_DETERM o etac ctxt conjE,
                Lazy.force map_cong |> Drule.rotate_prems (2*num_prems) |> etac ctxt] @
                subs_VT (etac ctxt @{thm bspec} THEN' assume_tac ctxt) (rtac ctxt refl) @
                [REPEAT_DETERM_N (2*num_prems) o assume_tac ctxt] |> EVERY1))
            |> Thm.close_derivation \<^here>
          end;

        val map_cong_pred = Lazy.lazy mk_map_cong_pred;

        fun mk_rel_map () =
          let
            fun mk_goal lhs rhs Ss fs =
              fold_rev Logic.all ([x, y] @ Ss @ fs) (mk_Trueprop_eq (lhs, rhs));

            val lhss =
              [Term.list_comb (relCsBs, S_CsBs) $
                  (Term.list_comb (mrbnf_map_AsCs, lis_id) $ x) $ y,
                Term.list_comb (relAsCs, S_AsCs) $ x $
                  (Term.list_comb (mrbnf_map_BsCs, lgs_id) $ y)];
            val rhss =
              [Term.list_comb (rel, @{map 3} (fn f => fn P => fn T =>
                 mk_vimage2p f (HOLogic.id_const T) $ P) lis S_CsBs lBs') $ x $ y,
               Term.list_comb (rel, @{map 3} (fn f => fn P => fn T =>
                 mk_vimage2p (HOLogic.id_const T) f $ P) lgs S_AsCs lAs') $ x $ y];
            val goals = @{map 4} mk_goal lhss rhss [S_CsBs, S_AsCs] [lis, lgs];
          in
            goals
            |> map (fn goal => prove_sorry "rel_map" lthy [] [] goal
              (fn {context = ctxt, prems = _} =>
                 mk_mr_rel_map0_tac ctxt live (Lazy.force rel_OO) (Lazy.force rel_conversep)
                   (Lazy.force rel_Grp) (Lazy.force map_id)))
            |> map (unfold_thms lthy @{thms vimage2p_def[of id, simplified id_apply]
                 vimage2p_def[of _ id, simplified id_apply]})
            |> map (Thm.close_derivation \<^here>)
          end;

        val rel_map = Lazy.lazy mk_rel_map;

        fun mk_rel_refl () = @{thm ge_eq_refl[OF ord_eq_le_trans]} OF
          [Lazy.force rel_eq RS sym, Lazy.force rel_mono OF (replicate live @{thm refl_ge_eq})];

        val rel_refl = Lazy.lazy mk_rel_refl;

        fun mk_rel_refl_strong () =
          (rule_by_tactic lthy (ALLGOALS (Object_Logic.full_atomize_tac lthy))
            ((Lazy.force rel_eq RS @{thm predicate2_eqD}) RS @{thm iffD2[OF _ refl]} RS
              Lazy.force rel_mono_strong)) OF
            (replicate live @{thm diag_imp_eq_le})

        val rel_refl_strong = Lazy.lazy mk_rel_refl_strong;

        fun mk_rel_preserves mk_prop prop_conv_thm thm () =
          let
            val Rs = map2 retype_const_or_free self_pred2RTs Rs;
            val prems = map (HOLogic.mk_Trueprop o mk_prop) Rs;
            val goal = HOLogic.mk_Trueprop (mk_prop (Term.list_comb (relAsAs, Rs)));
        val vars = fold (Variable.add_free_names lthy) (goal :: prems) [];
          in
            prove_sorry "rel_preserves" lthy vars [] (Logic.list_implies (prems, goal))
              (fn {context = ctxt, prems = _} =>
                unfold_thms_tac ctxt [prop_conv_thm] THEN
                HEADGOAL (rtac ctxt (Lazy.force thm RS sym RS @{thm ord_eq_le_trans})
                  THEN' rtac ctxt (Lazy.force rel_mono) THEN_ALL_NEW assume_tac ctxt))
            |> Thm.close_derivation \<^here>
          end;

        val rel_reflp = Lazy.lazy (mk_rel_preserves mk_reflp @{thm reflp_eq} rel_eq);
        val rel_symp = Lazy.lazy (mk_rel_preserves mk_symp @{thm symp_conversep} rel_conversep);
        val rel_transp = Lazy.lazy (mk_rel_preserves mk_transp @{thm transp_relcompp} rel_OO);

        fun mk_pred_True () =
          let
            val lhs = Term.list_comb (pred, map (fn T => absdummy T @{term True}) lAs');
            val rhs = absdummy CA' @{term True};
            val goal = mk_Trueprop_eq (lhs, rhs);
          in
            prove_sorry "pred_True" lthy [] [] goal
              (fn {context = ctxt, prems = _} =>
                map (rtac ctxt) [ext, Lazy.force pred_rel RS trans,
                  Lazy.force rel_cong0 RS fun_cong RS fun_cong RS trans OF
                    replicate live @{thm eq_onp_True}, Lazy.force rel_eq RS fun_cong RS fun_cong RS
                      trans, @{thm eqTrueI[OF refl]}] |> EVERY1)
            |> Thm.close_derivation \<^here>
          end;

        val pred_True = Lazy.lazy mk_pred_True;

        fun mk_pred_map () =
          let
            val lhs = Term.list_comb (pred', Qs) $ (Term.list_comb (mrbnf_map_AsBs, fs) $ x);
            val rhs = Term.list_comb (pred, map2 (curry HOLogic.mk_comp) Qs lfs) $ x;
            val goal = mk_Trueprop_eq (lhs, rhs) |> prems_fs;
            val vars = Variable.add_free_names lthy goal [];
            val pred_set = #pred_set axioms RS fun_cong RS sym;
          in
            prove_sorry "pred_map" lthy vars [] goal
              (fn {context = ctxt, prems = _} =>
                HEADGOAL (rtac ctxt (pred_set RSN (2, pred_set RSN (2, box_equals)))) THEN
                unfold_thms_tac ctxt
                  (@{thms Ball_image_comp ball_empty} @ map Lazy.force set_map) THEN
                HEADGOAL (rtac ctxt refl))
            |> Thm.close_derivation \<^here>
          end;

        val pred_map = Lazy.lazy mk_pred_map;
        val pred_map_id = Lazy.lazy (fn () => mk_pred_map () |> id_prems
          |> unfold_thms lthy [Lazy.force map_id]);

        fun mk_map_transfer () =
          let
            val rels = map2 mk_rel_fun transfer_domRs transfer_ranRs;
            val rel = mk_rel_fun
              (Term.list_comb (mk_mrbnf_rel transfer_domRTs CA' CB1, transfer_domRs))
              (Term.list_comb (mk_mrbnf_rel transfer_ranRTs CB' CB2, transfer_ranRs));
            val concl = HOLogic.mk_Trueprop (add_map_transfer_prems var_types (comb_frels fs rels)
              rel $ mrbnf_map_AsBs $ mk_mrbnf_map B1Ts B2Ts);

            val map_comp = Lazy.force map_comp;
            val map_comp_f_id = map_comp
              |> Drule.rotate_prems num_prems
              |> id_prems
              |> unfold_thms lthy @{thms id_o};
            val map_comp_id_f = map_comp
              |> id_prems
              |> unfold_thms lthy @{thms o_id};
            val map_cong_comp = (@{thm box_equals} OF
              [#map_cong0 axioms, map_comp_f_id RS sym, map_comp_id_f RS sym])
              |> Drule.rotate_prems (2*num_prems)
              |> simp_cong0_prems;
          in
            prove_sorry "map_transfer" lthy [] []
              (fold_rev Logic.all (transfer_domRs @ transfer_ranRs) concl)
              (fn {context = ctxt, prems = _} => mk_mr_map_transfer_tac ctxt non_dead num_prems
                (Lazy.force rel_mono) (Lazy.force in_rel_id)
                (map Lazy.force set_map |> filter_lives) map_cong_comp)
            |> Thm.close_derivation \<^here>
          end;

        val map_transfer = Lazy.lazy mk_map_transfer;

        fun mk_pred_transfer () =
          let
            val iff = HOLogic.eq_const HOLogic.boolT;
            val prem_rels = map (fn T => mk_rel_fun T iff) Rs;
            val prem_elems = mk_rel_fun (Term.list_comb (rel, Rs)) iff;
            val goal = HOLogic.mk_Trueprop
              (fold_rev mk_rel_fun prem_rels prem_elems $ pred $ pred');
            val vars = Variable.add_free_names lthy goal [];
          in
            prove_sorry "pred_transfer" lthy vars [] goal (fn {context = ctxt, prems = _} =>
              mk_pred_transfer_tac ctxt live (Lazy.force in_rel_id) (Lazy.force pred_map_id)
                (Lazy.force pred_cong))
            |> Thm.close_derivation \<^here>
          end;

        val pred_transfer = Lazy.lazy mk_pred_transfer;

        fun mk_rel_transfer () =
          let
            val iff = HOLogic.eq_const HOLogic.boolT;
            val prem_rels =
              map2 (fn T1 => fn T2 => mk_rel_fun T1 (mk_rel_fun T2 iff)) S_AsCs S_BsEs;
            val prem_elems =
              mk_rel_fun (Term.list_comb (mk_mrbnf_rel pred2RTsAsCs CA' CC', S_AsCs))
                (mk_rel_fun (Term.list_comb (mk_mrbnf_rel pred2RTsBsEs CB' CE', S_BsEs)) iff);
            val goal =
              HOLogic.mk_Trueprop (fold_rev mk_rel_fun prem_rels prem_elems $ rel $ relCsEs);
            val vars = Variable.add_free_names lthy goal [];
          in
            prove_sorry "rel_transfer" lthy vars [] goal
              (fn {context = ctxt, prems = _} =>
                mk_rel_transfer_tac ctxt (Lazy.force in_rel_id) (Lazy.force rel_map)
                  (Lazy.force rel_mono_strong))
            |> Thm.close_derivation \<^here>
          end;

        val rel_transfer = Lazy.lazy mk_rel_transfer;

        fun mk_set_transfer () =
          let
            val rel_sets = map2 (fn A => fn B => mk_rel 1 0 0 [A] [B] @{term rel_set}) lAs' lBs';
            val rel_Rs = Term.list_comb (rel, Rs);
            val goals = @{map 4} (fn R => fn rel_set => fn setA => fn setB => HOLogic.mk_Trueprop
              (mk_rel_fun rel_Rs (rel_set $ R) $ setA $ setB))
              Rs rel_sets mrbnf_sets_lAs mrbnf_sets_lBs;
          in
            if null goals then []
            else
              let
                val goal = Logic.mk_conjunction_balanced goals;
                val vars = Variable.add_free_names lthy goal [];
              in
                prove_sorry "set_transfer" lthy vars [] goal
                  (fn {context = ctxt, prems = _} =>
                     mk_set_transfer_tac ctxt (Lazy.force in_rel_id) set_map_id)
                |> Thm.close_derivation \<^here>
                |> Conjunction.elim_balanced (length goals)
              end
          end;

        val set_transfer = Lazy.lazy mk_set_transfer;

        fun mk_inj_map_strong () =
          let
            val assms = @{map 5} (fn setA => fn z => fn f => fn z' => fn f' =>
              fold_rev Logic.all [z, z']
                (Logic.mk_implies (mk_Trueprop_mem (z, setA $ x),
                   Logic.mk_implies (mk_Trueprop_mem (z', setA $ x'),
                     Logic.mk_implies (mk_Trueprop_eq (f $ z, f' $ z'),
                       mk_Trueprop_eq (z, z')))))) mrbnf_sets_lAs lzs lfs lzs' lfs';
            val concl = Logic.mk_implies
              (mk_Trueprop_eq
                 (Term.list_comb (mrbnf_map_AsBs, lfs_id) $ x,
                  Term.list_comb (mrbnf_map_AsBs, lfs'_id) $ x'),
               mk_Trueprop_eq (x, x'));
            val goal = fold_rev Logic.all (x :: x' :: lfs @ lfs')
              (fold_rev (curry Logic.mk_implies) assms concl);
          in
            prove_sorry "inj_map_strong" lthy [] [] goal (fn {context = ctxt, prems = _} =>
              mk_inj_map_strong_tac ctxt (Lazy.force rel_eq) (Lazy.force rel_map)
                (Lazy.force rel_mono_strong))
            |> Thm.close_derivation \<^here>
          end;

        val inj_map_strong = Lazy.lazy mk_inj_map_strong;

        val fsRs = comb_frels fs Rs;
        val fsRs_copy = comb_frels fs Rs_copy;
        val fs_copyRs_copy = comb_frels fs_copy Rs_copy;
        val gsSs = comb_frels gs Ss;
        val prem_terms_fs = mk_mrbnf_prem_terms fs;
        val prem_terms_gs = mk_mrbnf_prem_terms gs;
        val prem_terms_fsgs = prem_terms_fs @ prem_terms_gs;
        val prem_terms_fsfs_copy = prem_terms_fs @ mk_mrbnf_prem_terms fs_copy;

        fun mk_rel_map_non_lives () =
          let
            val map_As = Term.list_comb (mrbnf_map_AsAs, map2_VT (K HOLogic.id_const) K fs As') $ x;
            val map_Bs = Term.list_comb
              (mk_mrbnf_map Bs' Bs', map2_VT (K HOLogic.id_const) K fs Bs') $ y;
            val concl = Term.list_comb (rel, Rs @ [map_As, map_Bs]) |> HOLogic.mk_Trueprop;
            val prem = Term.list_comb (rel, Rs @ [x, y]) |> HOLogic.mk_Trueprop;

            val vars = map (fst o dest_Free) (fsRs @ [x, y]);
            val goal = Logic.mk_implies (prem, concl);

            fun exI_z z = infer_instantiate' lthy [NONE, SOME z] @{thm exI};
          in
            prove_sorry "rel_map_non_lives" lthy vars prem_terms_fs goal (fn {context = ctxt, prems = assms} =>
              mk_mr_rel_map_non_lives_tac ctxt live assms id_thms rel_OO_Grp
                (Lazy.force rel_OO_Grp_id) (Lazy.force map_id) (Lazy.force map_comp) exI_z)
            |> Thm.close_derivation \<^here>
          end;

        val rel_map_non_lives = Lazy.lazy mk_rel_map_non_lives;

        val ((mrbnf_rel_name, mrbnf_rel, mrbnf_rel_def), lthy) =
          let
            val map_x = Term.list_comb
              (mrbnf_map_AsAs, map2_VT (K HOLogic.id_const) K fs As' @ [x]);
            val rhs = Term.list_comb (rel, Rs @ [map_x, y])
              |> fold_rev (Term.absfree o dest_Free) (fsRs @ [x, y]);
          in
            new_definition (Binding.prefix_name (mr_relN ^ "_") mrbnf_b) rhs lthy
          end;

        fun mk_mrbnf_rel As Bs CA CB =
          normalize_rel lthy (map2_VT mk_pred2T (curry op -->) As Bs) CA CB mrbnf_rel;


        val mrrelAsAs = mk_mrbnf_rel As' As' CA' CA';
        val mrrelAsBs = mk_mrbnf_rel As' Bs' CA' CB';
        val mrrelBsAs = mk_mrbnf_rel Bs' As' CB' CA';
        val mrrelAsCs = mk_mrbnf_rel As' Cs CA' CC';
        val mrrelBsCs = mk_mrbnf_rel Bs' Cs CB' CC';
        val mrrelBsEs = mk_mrbnf_rel Bs' Es CB' CE';
        val mrrelCsEs = mk_mrbnf_rel Cs Es CC' CE';

        fun mk_mr_rel_eq () =
          let
            val lhs = Term.list_comb (mrrelAsAs, map_VT HOLogic.eq_const HOLogic.id_const As');
            val goal = HOLogic.mk_eq (lhs, HOLogic.eq_const CA') |> HOLogic.mk_Trueprop;
          in
            prove_sorry "mr_rel_eq" lthy [] [] goal (fn {context = ctxt, prems = _} => EVERY1 [
              K (Local_Defs.unfold0_tac ctxt [mrbnf_rel_def, Lazy.force map_id]),
              rtac ctxt (Lazy.force rel_eq)
            ]) |> Thm.close_derivation \<^here>
          end;

        val mr_rel_eq = Lazy.lazy mk_mr_rel_eq;

        fun mk_mr_le_rel_OO () =
          let
            val rel_OO_lhs = mk_rel_compp
              (Term.list_comb (mrrelAsBs, fsRs), Term.list_comb (mrrelBsCs, gsSs));
            val rel_OO_rhs = Term.list_comb
              (mrrelAsCs, zip_map_VT mk_rel_compp (HOLogic.mk_comp o swap) fsRs gsSs);

            val vars = map (fst o dest_Free) (fsRs @ gsSs);
            val goal = mk_leq rel_OO_lhs rel_OO_rhs
              |> HOLogic.mk_Trueprop;

           fun mk_map_comp assms = if non_dead = live then Lazy.force map_id else
             (Lazy.force map_comp OF assms) RS sym;
          in
            prove_sorry "mr_le_rel_OO" lthy vars prem_terms_fsgs goal (fn {context = ctxt, prems = assms} =>
              mk_mr_le_rel_OO_tac ctxt num_prems assms mrbnf_rel_def mk_map_comp (#le_rel_OO axioms)
                (Lazy.force rel_map_non_lives) (#map_id0 axioms))
            |> Thm.close_derivation \<^here>
          end;

        val mr_le_rel_OO = Lazy.lazy mk_mr_le_rel_OO;

        fun mk_mr_in_rel () =
          let
            val RTs = zip_map_VT HOLogic.mk_prodT fst As' Bs';
            val setRs = @{map 3} (fn R => fn T => fn U => HOLogic.Collect_const
              (HOLogic.mk_prodT (T, U)) $ HOLogic.mk_case_prod R) Rs lAs' lBs';
            val sets = map (mk_mrbnf_t RTs) (filter_lives mrbnf_sets);

            val map_x = Term.list_comb
              (mk_mrbnf_map RTs As', map_VT fst_const HOLogic.id_const RTs);
            val map_y = Term.list_comb (mk_mrbnf_map RTs Bs', map2_VT (K snd_const) K fs RTs);
            fun mk_ex As sets T =
              let
                val z = yield_singleton (mk_Frees "z") T frees_lthy |> fst;
              in
                HOLogic.mk_exists (dest_Free z |> fst, T, foldr1 HOLogic.mk_conj
                  ((if null sets then [HOLogic.mk_mem (z, HOLogic.mk_UNIV T)]
                    else map2 (fn t => mk_leq (t $ z)) sets As)
                    @ map HOLogic.mk_eq [(map_x $ z, x), (map_y $ z, y)]))
              end;

            val lhs = Term.list_comb (mrrelAsBs, fsRs @ [x, y]);
            val rhs = mk_ex setRs sets (mk_mrbnf_T RTs Calpha);
            val vars = map (fst o dest_Free) (fsRs @ [x, y]);
            val goal = mk_Trueprop_eq (lhs, rhs);
          in
            prove_sorry "mr_in_rel" lthy vars prem_terms_fs goal (fn {context = ctxt, prems = assms} => EVERY1 [
              K (Local_Defs.unfold0_tac ctxt [mrbnf_rel_def]),
              rtac ctxt (trans OF [rel_OO_Grp OF assms]),
              rtac ctxt @{thm trans[OF OO_Grp_alt[THEN fun_cong, THEN fun_cong]]},
              K (Local_Defs.unfold0_tac ctxt @{thms mem_Collect_eq conj_assoc}),
              rtac ctxt refl
            ]) |> Thm.close_derivation \<^here>
          end;

        val mr_in_rel = Lazy.lazy mk_mr_in_rel;

        val mk_mrbnf_terms_map = `(map_split (dest_funT o fastype_of) #> uncurry mk_mrbnf_map)
          #> Term.list_comb;

        fun mk_mr_rel_OO () =
          let
            val someI2_ex1 = @{thm someI2_ex[of "\<lambda>b. R _ b \<and> S b _" "\<lambda>b. T _ b" for R S T]};
            val someI2_ex2 = @{thm someI2_ex[of "\<lambda>b. R _ b \<and> S b _" "\<lambda>b. T b _" for R S T]};
            fun mk_someI2_exs someI2_ex Xs = (Rs ~~ Ss) ~~ Xs |> map (fn ((a, b), c) =>
              thm_instantiate_terms lthy [SOME a, NONE, SOME b, NONE, SOME c] someI2_ex);
            val someI2_exs = mk_someI2_exs someI2_ex1 Rs @ mk_someI2_exs someI2_ex2 Ss;

            fun conj_rel do_swap R1 R2 Tx Ty =
              let
                val ((x, y), w) = frees_lthy
                  |> yield_singleton (mk_Frees "x") Tx
                  ||>> yield_singleton (mk_Frees "y") Ty
                  ||>> yield_singleton (mk_Frees "w") (fst_binder_type R2)
                  |> fst;
              in
                HOLogic.mk_conj (R1 $ x $ w, R2 $ w $ y)
                  |> Term.absfree (dest_Free w)
                  |> (fn t => HOLogic.choice_const (fastype_of w) $ t)
                  |> curry (do_swap ? swap #> HOLogic.mk_prod) (if do_swap then y else x)
                  |> fold_rev (Term.absfree o dest_Free) [x, y]
                  |> HOLogic.mk_case_prod
              end;
            fun mk_exI do_swap z =
              let
                val relfs = @{map 4} (conj_rel do_swap) Rs Ss lAs' lCs
                  |> comb_frels (if do_swap then fs else map HOLogic.id_const As')
                  |> mk_mrbnf_terms_map;
              in
                thm_instantiate_terms lthy [NONE, SOME (relfs $ Thm.term_of z)] @{thm exI}
              end;
            val mk_exIs = fold_map (mk_exI #> `) [false, true] #> fst;

            val rel_OO_lhs = Term.list_comb
              (mrrelAsCs, zip_map_VT mk_rel_compp (HOLogic.mk_comp o swap) fsRs gsSs);
            val rel_OO_rhs = mk_rel_compp
              (Term.list_comb (mrrelAsBs, fsRs), Term.list_comb (mrrelBsCs, gsSs));

            val vars = map (fst o dest_Free) (fsRs @ gsSs);
            val goal = mk_Trueprop_eq (rel_OO_lhs, rel_OO_rhs);
          in
            prove_sorry "mr_rel_OO" lthy vars prem_terms_fsgs goal (fn {context = ctxt, prems = assms} =>
              mk_mr_rel_OO_tac ctxt assms id_thms (Lazy.force mr_le_rel_OO) (Lazy.force mr_in_rel)
                supp_comp_bound mk_exIs (map Lazy.force set_map) (Lazy.force map_comp) someI2_exs
                (#map_cong0 axioms))
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_OO = Lazy.lazy mk_mr_rel_OO;

        fun mk_mr_rel_mono () =
          let
            fun mk_mr_rel_concl f = HOLogic.mk_Trueprop
              (f (Term.list_comb (mrrelAsBs, fsRs), Term.list_comb (mrrelAsBs, fsRs_copy)));
            val vars = map (fst o dest_Free) (fsRs @ Rs_copy);
            val prems = prem_terms_fs @ mk_rel_prems mk_leq;
            val goal = mk_mr_rel_concl (uncurry mk_leq);
          in
            prove_sorry "mr_rel_mono" lthy vars prems goal (fn {context = ctxt, prems = assms} =>
              mk_mr_rel_mono_tac ctxt (chop num_prems assms) (Lazy.force mr_in_rel))
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_mono = Lazy.lazy mk_mr_rel_mono;

        fun mk_mr_rel_cong0 () =
          let
            fun mk_mr_rel_concl f = HOLogic.mk_Trueprop
              (f (Term.list_comb (mrrelAsBs, fsRs), Term.list_comb (mrrelAsBs, fsRs_copy)));
            val vars = map (fst o dest_Free) (fsRs @ Rs_copy);
            val prems = mk_rel_prems (curry HOLogic.mk_eq);
            val goal = mk_mr_rel_concl HOLogic.mk_eq;
          in
            prove_sorry "mr_rel_cong0" lthy vars [] (Logic.list_implies (prems, goal))
              (fn {context = ctxt, prems = _} => (TRY o hyp_subst_tac ctxt THEN' rtac ctxt refl) 1)
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_cong0 = Lazy.lazy mk_mr_rel_cong0;

        fun mk_mr_rel_cong () =
          let
            val prem0 = mk_Trueprop_eq (x, x_copy);
            val prem1 = mk_Trueprop_eq (y, y_copy);
            val fprems = @{map 4} (mk_map_cong_prem Logic.mk_implies x_copy) zs mrbnf_sets_As fs fs_copy;
            val fprems = map_filter I (map2 (fn Live_Var => (fn _ => NONE) | _ => fn x => SOME x) var_types fprems)
            val Rprems = @{map 6} (mk_rel_cong_prem Logic.mk_implies x_copy y_copy)
              lzs lys mrbnf_sets_lAs mrbnf_sets_lBs Rs Rs_copy;
            val eq = mk_Trueprop_eq (Term.list_comb (mrrelAsBs, fsRs) $ x $ y,
              Term.list_comb (mrrelAsBs, fs_copyRs_copy) $ x_copy $ y_copy);
            val goal = prems_fsfs_copy (Logic.list_implies (prem0 :: prem1 :: fprems @ Rprems, eq));
          in
            fold (Variable.add_free_names lthy) (eq :: prem0 :: prem1 :: fprems @ Rprems) []
            |> (fn vars => prove_sorry "mr_rel_cong" lthy vars [] goal (fn {context = ctxt, ...} => EVERY1 [
                K (unfold_thms_tac ctxt [mrbnf_rel_def]),
                rtac ctxt (Lazy.force rel_cong),
                rtac ctxt (Lazy.force map_cong),
                REPEAT_DETERM o FIRST' [
                  assume_tac ctxt,
                  Goal.assume_rule_tac ctxt,
                  rtac ctxt refl,
                  EVERY' [
                    EqSubst.eqsubst_asm_tac ctxt [0] (map Lazy.force set_map),
                    REPEAT_DETERM o assume_tac ctxt,
                    K (unfold_thms_tac ctxt @{thms image_id})
                  ]
                ]
              ]))
            |> Thm.close_derivation \<^here>
          end;
        val mr_rel_cong = Lazy.lazy mk_mr_rel_cong;

        fun mk_mr_rel_Grp () =
          let
            val lhs = Term.list_comb (mrrelAsBs, map2_VT mk_Grp (K I) As fs);
            val rhs = mk_Grp (mk_in lAs mrbnf_sets_lAs CA') (Term.list_comb (mrbnf_map_AsBs, fs));

            fun live_map_fun f =
              let
                val a = yield_singleton (mk_Frees "a") (fst_binder_type f) frees_lthy |> fst;
              in
                HOLogic.mk_prod (a, f $ a) |> Term.absfree (dest_Free a)
              end;
            val inst_term = map_VT live_map_fun I lfs_id |> mk_mrbnf_terms_map |> add_dummy;
            val exI_inst = thm_instantiate_dummy_terms lthy [NONE, SOME inst_term] exI;

            val vars = map (fst o dest_Free) (lAs @ fs);
            val goal = mk_Trueprop_eq (lhs, rhs);
          in
            prove_sorry "mr_rel_Grp" lthy vars prem_terms_fs goal (fn {context = ctxt, prems = assms} =>
              mk_mr_rel_Grp_tac ctxt assms (Lazy.force mr_in_rel) (Lazy.force map_comp)
                (map Lazy.force set_map) (#map_cong0 axioms) (#map_id0 axioms) exI_inst id_thms)
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_Grp = Lazy.lazy mk_mr_rel_Grp;

        fun mk_mr_rel_conversep () =
          let
            val lhs = Term.list_comb (mrrelBsAs, map_VT mk_conversep mk_inv fsRs);
            val rhs = mk_conversep (Term.list_comb (mrrelAsBs, fsRs));
            val vars = map (fst o dest_Free) fsRs;
            val bij_prems = mk_prem_terms (subs_VT Live_Var Bound_Var) fs;
            val goal = mk_Trueprop_eq (lhs, rhs);

            fun swap_term Ta Tb =
              let
                val (a, b) = frees_lthy
                  |> yield_singleton (mk_Frees "a") Ta
                  ||>> yield_singleton (mk_Frees "b") Tb
                  |> fst;
              in
                HOLogic.mk_prod (b, a)
                |> fold_rev (Term.absfree o dest_Free) [a, b]
                |> HOLogic.mk_case_prod
              end;
            fun add_swap_terms lAs' lBs' fs = map2 swap_term lAs' lBs'
              |> comb_frels fs
              |> mk_mrbnf_terms_map;
            fun exI_t_z lAs' lBs' fs z = thm_instantiate_dummy_terms lthy
              [NONE, SOME (add_swap_terms lAs' lBs' fs $ Thm.term_of z)] exI;

            val exI_z1 = exI_t_z lAs' lBs' fs;
            val exI_z2 = map mk_inv fs |> exI_t_z lBs' lAs';
          in
            prove_sorry "mr_rel_conversep" lthy vars bij_prems goal (fn {context = ctxt, prems = assms} =>
              let
                val prems = fold (fn var_type => fn (xs, ys) => case var_type of
                  Free_Var => (drop 2 xs, nth xs 1::ys)
                  | Bound_Var => (drop 2 xs, nth xs 1::nth xs 0::ys)
                  | _ => (xs, ys)
                ) var_types (assms, []) |> snd |> rev
                val inv_prems = fold (fn var_type => fn (xs, ys) => case var_type of
                  Free_Var => (drop 2 xs, (@{thm supp_inv_bound} OF (take 2 xs))::ys)
                  | Bound_Var => let val (bij::supp::xs') = xs
                    in (xs', (@{thm supp_inv_bound} OF [bij, supp])::(@{thm bij_imp_bij_inv} OF [bij])::ys) end
                  | _ => (xs, ys)
                ) var_types (assms, []) |> snd |> rev
              in
                mk_mr_rel_conversep_tac ctxt assms prems id_thms inv_prems (Lazy.force mr_in_rel) supp_comp_bound
                  (Lazy.force map_comp) (map Lazy.force set_map) (#map_cong0 axioms) exI_z1 exI_z2
              end
            )
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_conversep = Lazy.lazy mk_mr_rel_conversep;

        fun mk_mr_rel_map_left () =
          let
            val lhs = Term.list_comb (mrrelBsCs, gsSs) $
              Term.list_comb (mrbnf_map_AsBs, fs @ [x]) $ z;
            val mk_Grp_compp = `fastype_of #>> HOLogic.mk_UNIV o fst o dest_funT #-> mk_Grp
              |> apsnd #> swap #> mk_rel_compp;
            val rhs = Term.list_comb (mrrelAsCs, zip_map_VT mk_Grp_compp HOLogic.mk_comp gsSs fs) $
              x $ z;
            val vars = map (fst o dest_Free) (fs @ gsSs @ [x, z]);
            val goal = mk_Trueprop_eq (lhs, rhs);
          in
            prove_sorry "mr_rel_map_left" lthy vars prem_terms_fsgs goal (fn {context = ctxt, prems = assms} =>
              mk_mr_rel_map_left_tac ctxt assms (Lazy.force mr_rel_OO) (Lazy.force mr_rel_Grp))
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_map_left = Lazy.lazy mk_mr_rel_map_left;

        fun mk_mr_rel_map_right () =
          let
            val lhs = Term.list_comb (mrrelAsBs, fsRs) $ x $ y;
            val mk_Grp_compp = `fastype_of #>> HOLogic.mk_UNIV o fst o dest_funT #-> mk_Grp
              |> apfst #> swap #> mk_rel_compp;
            val rhs = Term.list_comb (mrrelAsCs, zip_map_VT mk_Grp_compp HOLogic.mk_comp gs fsRs) $
              x $ Term.list_comb (mrbnf_map_BsCs, gs @ [y]);
            val vars = map (fst o dest_Free) (fsRs @ gs @ [x, y]);
            val goal = apply2 HOLogic.mk_Trueprop (lhs, rhs) |> Logic.mk_implies;
          in
            prove_sorry "mr_rel_map_right" lthy vars prem_terms_fsgs goal (fn {context = ctxt, prems = assms} =>
              mk_mr_rel_map_right_tac ctxt assms (Lazy.force mr_rel_OO) (Lazy.force mr_rel_Grp))
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_map_right = Lazy.lazy mk_mr_rel_map_right;

        fun mk_mr_rel_map_right_bij () =
          let
            val lhs = Term.list_comb (mrrelAsBs, fsRs) $ x $
              Term.list_comb (mrbnf_map_AsBs, fs_copy @ [x_copy]);
            val mk_inv_o = mk_inv |> apfst #> HOLogic.mk_comp;
            val mk_Grp_compp = `fastype_of #>> HOLogic.mk_UNIV o fst o dest_funT #-> mk_Grp
              #> mk_conversep |> apfst #> swap #> mk_rel_compp;
            val rhs = Term.list_comb (mrrelAsAs, zip_map_VT mk_Grp_compp mk_inv_o fs_copy fsRs) $
              x $ x_copy;
            val vars = map (fst o dest_Free) (fsRs @ fs_copy @ [x, x_copy]);
            val bij_prems = mk_prem_terms (subs_VT Live_Var Bound_Var) fs_copy;
            val prems = prem_terms_fs @ bij_prems;
            val goal = mk_Trueprop_eq (lhs, rhs);
          in
            prove_sorry "mr_rel_map_right_bij" lthy vars prems goal (fn {context = ctxt, prems = assms} =>
              mk_mr_rel_map_right_bij_tac ctxt assms (Lazy.force mr_rel_OO) (Lazy.force map_comp)
                (Lazy.force mr_rel_conversep) (Lazy.force mr_rel_Grp))
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_map_right_bij = Lazy.lazy mk_mr_rel_map_right_bij;

        fun mk_mr_rel_map () = map Lazy.force
          [mr_rel_map_left, mr_rel_map_right, mr_rel_map_right_bij];

        val mr_rel_map = Lazy.lazy mk_mr_rel_map;

        fun mk_mr_map_transfer () =
          let
            val rels = map2 mk_rel_fun transfer_domRs transfer_ranRs;
            val rel = mk_rel_fun
              (Term.list_comb (mk_mrbnf_rel As' B1Ts CA' CB1, comb_frels lfs_id transfer_domRs))
              (Term.list_comb (mk_mrbnf_rel Bs' B2Ts CB' CB2, comb_frels lgs_id transfer_ranRs));
            val concl = HOLogic.mk_Trueprop (add_map_transfer_prems var_types (comb_frels fs rels)
              rel $ mrbnf_map_AsBs $ mk_mrbnf_map B1Ts B2Ts);
            val goal = fold_rev Logic.all (transfer_domRs @ transfer_ranRs) concl;
          in
            prove_sorry "mr_map_transfer" lthy [] [] goal (fn {context = ctxt, prems = _} =>
              unfold_tac ctxt [mrbnf_rel_def, Lazy.force map_id, Lazy.force map_transfer])
            |> Thm.close_derivation \<^here>
          end;

        val mr_map_transfer = Lazy.lazy mk_mr_map_transfer;

        fun mk_mr_rel_transfer () =
          let
            val iff = HOLogic.eq_const HOLogic.boolT;
            val prem_rels =
              map2 (fn T1 => fn T2 => mk_rel_fun T1 (mk_rel_fun T2 iff)) S_AsCs S_BsEs;
            val prem_elems =
              mk_rel_fun (Term.list_comb (mrrelAsCs, comb_frels lis_id S_AsCs))
                (mk_rel_fun (Term.list_comb (mrrelBsEs, comb_frels lis_id S_BsEs)) iff);
            val goal =
              HOLogic.mk_Trueprop (add_map_transfer_prems var_types (comb_frels fs prem_rels)
                prem_elems $ mrrelAsBs $ mrrelCsEs);
            val vars = Variable.add_free_names lthy goal [];

            val mr_rel_monos =
              let
                val mr_rel_mono' = Drule.rotate_prems ~1 (Lazy.force mr_rel_mono RS
                  @{thm predicate2D}) OF [Lazy.force mr_le_rel_OO RS @{thm predicate2D}];
                fun add_ids b = (b ? swap) (id_prems, Drule.rotate_prems num_prems) |> op o;
                fun mk_mr_rel_monos b = unfold_thms lthy @{thms id_o o_id}
                  (add_ids b mr_rel_mono' OF @{thms relcomppI});
              in
                apply2 mk_mr_rel_monos (false, true)
              end;
            val mr_rel_conversep' = (Lazy.force mr_rel_conversep
                |> bij_id_prems RS @{thm predicate2_eqD} RS @{thm iffD2})
              |> unfold_thms lthy @{thms conversep_iff[abs_def] inv_id}
              |> Drule.rotate_prems ~1;
            fun mk_trans_theorems do_swap =
              (mr_rel_monos |> do_swap ? swap |> list_of_pair) @ [mr_rel_conversep'];
          in
            prove_sorry "mr_rel_transfer" lthy vars [] goal (fn {context = ctxt, prems = _} =>
              mk_mr_rel_transfer_tac ctxt live mk_trans_theorems)
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_transfer = Lazy.lazy mk_mr_rel_transfer;

        fun mk_mr_rel_OO_Grp () =
          let
            val vars = map (fst o dest_Free) fsRs;
            val goal = mk_Trueprop_eq (Term.list_comb (mrrelAsBs, fsRs),
              Term.list_comb (mk_rel_spec Ds fs, Rs));
          in
            prove_sorry "mr_rel_OO_Grp" lthy vars prem_terms_fs goal (fn {context = ctxt, prems = assms} =>
              simp_only_tac ctxt [mrbnf_rel_def, #rel_OO_Grp axioms OF assms, ext] |> HEADGOAL)
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_OO_Grp = Lazy.lazy mk_mr_rel_OO_Grp;

        (* TODO: See if this really works *)
        (*fun register_bnf lthy =
          let
            val mrbnf_rel_b = Binding.name mrbnf_rel_name;
            val map_id_AsBs = Term.list_comb (mrbnf_map_AsBs, lfs_id)
              |> fold_rev Term.absfree (map dest_Free lfs);
            val rel_id_AsBs = Term.list_comb (mrrelAsBs, comb_frels lfs_id Rs)
              |> fold_rev Term.absfree (map dest_Free Rs);
            val tacs = map (fn thm => fn ctxt =>
              rtac ctxt thm THEN_ALL_NEW Goal.assume_rule_tac ctxt |> HEADGOAL)
              ([#map_id0 axioms, map_comp0_id, map_cong0_id] @
                (#set_map0 axioms |> filter_lives |> map id_prems) @
                [bd_card_order, bd_cinfinite] @ (filter_lives weak_set_bd) @
                [Lazy.force mr_le_rel_OO |> simp_comp_thm lthy,
                  Lazy.force mr_rel_OO_Grp |> id_prems, #pred_set axioms]);
            fun wit_tac ctxt = flat wit_thms |> map
              (fn thm => rtac ctxt thm THEN_ALL_NEW assume_tac ctxt) |> EVERY1;
          in
            BNF_Def.bnf_def BNF_Def.Do_Inline (K BNF_Def.Dont_Note) internal qualify tacs wit_tac
              (SOME (Ds @ filter_non_lives As')) map_b mrbnf_rel_b pred_b set_bs
              (((((((Binding.prefix false "Bnf" raw_mrbnf_b, CA'), map_id_AsBs), mrbnf_sets_lAs),
                mrbnf_bd_As), map snd mrbnf_wit_As), SOME rel_id_AsBs), SOME pred) lthy
          end;

        val lthy = if live > 0 andalso not internal then register_bnf lthy |> snd else lthy;*)

        fun mk_mr_rel_flip () =
          let
            val lhs = Term.list_comb (mrrelBsAs, map_VT mk_conversep mk_inv fsRs) $ y $ x;
            val rhs = Term.list_comb (mrrelAsBs, fsRs) $ x $ y;
            val vars = map (fst o dest_Free) (fsRs @ [x, y]);
            val bij_prems = mk_prem_terms (subs_VT Live_Var Bound_Var) fs;
            val goal = mk_Trueprop_eq (lhs, rhs);
          in
            prove_sorry "mr_rel_flip" lthy vars bij_prems goal (fn {context = ctxt, prems = assms} =>
              unfold_tac ctxt [Lazy.force mr_rel_conversep OF assms, @{thm conversep_iff}])
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_flip = Lazy.lazy mk_mr_rel_flip;

        fun mk_mr_set_transfer () =
          let
            val mk_image_Grp = mk_image #> `fastype_of #>> HOLogic.mk_UNIV o fst o dest_funT
              #-> mk_Grp;
            fun mk_rel_set R =
              let
                val (A, B) = fastype_of R |> binder_types |> dest_cons ||> hd;
              in
                mk_rel 1 0 0 [A] [B] @{term rel_set} $ R
              end;
            val rel_sets = map_VT mk_rel_set mk_image_Grp fsRs;
            val rel_Rs = Term.list_comb (mrrelAsBs, fsRs);
            val vars = map (fst o dest_Free) fsRs;
            val goals = @{map 3} (fn rel_set => fn setA => fn setB => HOLogic.mk_Trueprop
              (mk_rel_fun rel_Rs rel_set $ setA $ setB)) rel_sets mrbnf_sets_As mrbnf_sets_Bs;
          in
           goals
            |> map (fn goal => prove_sorry "mr_set_transfer" lthy vars prem_terms_fs goal
              (fn {context = ctxt, prems = assms} =>
                mk_mr_set_transfer_tac ctxt assms id_thms (Lazy.force mr_in_rel) (map Lazy.force set_map)))
            |> map (Thm.close_derivation \<^here>)
          end;

        val mr_set_transfer = Lazy.lazy mk_mr_set_transfer;

        fun mk_mr_rel_mono_strong0 () =
          let
            fun mk_live_prem setA setB R S a b =
              HOLogic.mk_Trueprop
                (mk_Ball (setA $ x) (Term.absfree (dest_Free a)
                  (mk_Ball (setB $ y) (Term.absfree (dest_Free b)
                    (HOLogic.mk_imp (R $ a $ b, S $ a $ b))))));
            fun mk_non_live_prem set _ f g a _ =
              HOLogic.mk_Trueprop
                (mk_Ball (set $ x) (Term.absfree (dest_Free a)
                  (HOLogic.mk_eq (f $ a, g $ a))));
            val mk_prems = subs_VT mk_live_prem mk_non_live_prem;
            val prems = HOLogic.mk_Trueprop (Term.list_comb (mrrelAsBs, fsRs) $ x $ y) ::
              @{map 7} I mk_prems mrbnf_sets_As mrbnf_sets_Bs fsRs fs_copyRs_copy zs ys;
            val vars = map (fst o dest_Free) (x :: y :: fsRs @ fs_copyRs_copy);
            val goal = Logic.list_implies (prems,
              HOLogic.mk_Trueprop (Term.list_comb (mrrelAsBs, fs_copyRs_copy) $ x $ y));
          in
            prove_sorry "mr_rel_mono_strong0" lthy vars prem_terms_fsfs_copy goal
              (fn {context = ctxt, prems = assms} =>
                mk_mr_rel_mono_strong0_tac ctxt assms id_thms (map Lazy.force set_map) (Lazy.force map_cong)
                  (Lazy.force mr_in_rel))
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_mono_strong0 = Lazy.lazy mk_mr_rel_mono_strong0;

        fun mk_mr_rel_mono_strong () =
          let
            fun mk_prem setA setB R S a b =
              HOLogic.mk_Trueprop
                (mk_Ball (setA $ x) (Term.absfree (dest_Free a)
                  (mk_Ball (setB $ y) (Term.absfree (dest_Free b)
                    (HOLogic.mk_imp (R $ a $ b, S $ a $ b))))));
            val prems = HOLogic.mk_Trueprop (Term.list_comb (mrrelAsBs, fsRs) $ x $ y) ::
              @{map 6} mk_prem mrbnf_sets_lAs mrbnf_sets_lBs Rs Rs_copy lzs lys;
            val vars = map (fst o dest_Free) (x :: y :: fsRs @ Rs_copy);
            val goal = Logic.list_implies (prems,
              HOLogic.mk_Trueprop (Term.list_comb (mrrelAsBs, fsRs_copy) $ x $ y));
          in
            prove_sorry "mr_rel_mono_strong" lthy vars prem_terms_fs goal
              (fn {context = ctxt, prems = assms} =>
                REPEAT_DETERM (FIRST1 [assume_tac ctxt, resolve_tac ctxt (@{thms ballI refl} @
                  [Lazy.force mr_rel_mono_strong0 OF (assms @ assms)])]))
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_mono_strong = Lazy.lazy mk_mr_rel_mono_strong;

        fun mk_mr_rel_id () =
          let
            val vars = map (fst o dest_Free) Rs;
            val goal = mk_Trueprop_eq (Term.list_comb (rel, Rs),
              Term.list_comb (mrrelAsBs, comb_frels lfs_id Rs));
          in
            prove_sorry "mr_rel_id" lthy vars [] goal (fn {context = ctxt, prems = _} =>
              simp_only_tac ctxt [mrbnf_rel_def, Lazy.force map_id] |> HEADGOAL)
            |> Thm.close_derivation \<^here>
          end;

        val mr_rel_id = Lazy.lazy mk_mr_rel_id;

        fun mk_mr_rel_set () =
          let
            val mr_prem = Logic.implies $ HOLogic.mk_Trueprop (Term.list_comb (mrrelAsBs, fsRs @ [x, y]))
            fun mk_var_goal setA setB i = mr_prem $ mk_Trueprop_eq (setB $ y, mk_image (nth fsRs i) $ (setA $ x))
            fun mk_live_goal setA setB B i = mr_prem $ (Logic.implies $
              HOLogic.mk_Trueprop (HOLogic.mk_mem (nth zs i, setA $ x)) $
              HOLogic.mk_Trueprop (mk_Bex (setB $ y) (Term.abs ("z'", B) (nth fsRs i $ nth zs i $ Bound 0)))
            );
            val vars = map (fst o dest_Free) (fsRs @ [x, y])
          in @{map 6} (fn setA => fn setB => fn B => fn var_type => fn set_transfer => fn i =>
            prove_sorry ("mr_rel_set" ^ string_of_int i) lthy (vars @ [fst (dest_Free (nth zs i))]) prem_terms_fs
              (if var_type = Live_Var then mk_live_goal setA setB B i else mk_var_goal setA setB i) (fn {context, prems} =>
              mk_mr_rel_set_tac context (var_type = Live_Var) set_transfer prems
            ) |> Thm.close_derivation \<^here>) mrbnf_sets_As mrbnf_sets_Bs Bs' var_types (Lazy.force mr_set_transfer) (0 upto non_dead - 1)
          end;

        val mr_rel_set = Lazy.lazy mk_mr_rel_set;

        val defs = mk_defs mrbnf_map_def mrbnf_set_defs mrbnf_rel_def mrbnf_rel_def mrbnf_pred_def;

        val facts = mk_facts bd_card_order bd_cinfinite bd_regularCard bd_Card_order bd_Cinfinite
          bd_Cnotzero collect_set_map in_bd in_cong in_mono in_rel inj_map inj_map_strong map_comp
          map_cong map_cong_simp map_cong_pred map_id map_ident0 map_ident map_transfer rel_eq
          rel_flip set_map set_bd_UNIV rel_cong0 rel_cong rel_cong_simp rel_map rel_mono rel_mono_strong0
          rel_mono_strong set_transfer rel_Grp rel_conversep rel_OO rel_OO_Grp_id rel_refl
          rel_refl_strong rel_reflp rel_symp rel_transp rel_transfer rel_eq_onp pred_transfer
          pred_True pred_map pred_rel pred_mono_strong0 pred_mono_strong pred_mono pred_cong0
          pred_cong pred_cong_simp;

        val mr_facts = mk_mr_facts var_large var_regular natLeq_bound UNIV_cinfinite supp_comp_bound
          Un_bound UNION_bound mr_rel_cong0 mr_rel_cong mr_in_rel mr_le_rel_OO mr_map_transfer mr_rel_eq mr_rel_flip
          mr_rel_map mr_rel_mono mr_rel_mono_strong0 mr_rel_mono_strong mr_set_transfer mr_rel_Grp
          mr_rel_conversep mr_rel_OO mr_rel_OO_Grp mr_rel_transfer mr_rel_id mr_rel_set;

        val wits = map2 mk_witness mrbnf_wits wit_thms;

        val mrbnf_rel =
          Term.subst_atomic_types ((Ds ~~ deads) @ (As' ~~ alphas) @ (Bs' ~~ betas)) rel;

        val mrbnf_mr_rel =
          Term.subst_atomic_types ((Ds ~~ deads) @ (As' ~~ alphas) @ (Bs' ~~ betas)) mrrelAsBs;

        val mrbnf_pred = Term.subst_atomic_types ((Ds ~~ deads) @ (As' ~~ alphas)) pred;

        val mrbnf = mk_mrbnf mrbnf_b Calpha
          var_types free frees bound bounds live lives lives' dead deads
          mrbnf_map mrbnf_sets mrbnf_bd class class_thms coclass axioms defs facts mr_facts wits
          mrbnf_rel mrbnf_mr_rel mrbnf_pred;

(*val _ = map (@{print} o Lazy.force) ([mr_rel_eq, mr_le_rel_OO, mr_in_rel, mr_rel_OO,
          mr_rel_mono, mr_rel_Grp, mr_rel_conversep, mr_rel_map_left, mr_rel_map_right,
          mr_rel_map_right_bij, mr_map_transfer, mr_rel_transfer, mr_rel_flip] @
          (Lazy.force mr_set_transfer |> map (fn thm => Lazy.lazy (fn () => thm))) @ [
          mr_rel_mono_strong0, mr_rel_mono_strong]);*)

(*val _ = map (@{print} o Lazy.force) [collect_set_map, in_bd, in_cong,
          in_mono, in_rel, inj_map, inj_map_strong, map_comp, map_cong, map_cong_simp, map_cong_pred, map_id,
          map_ident0, map_ident, map_transfer, rel_eq, rel_flip, (*set_map,*) rel_cong0, rel_cong, rel_cong_simp,
          (*rel_map,*) rel_mono, rel_mono_strong0, rel_mono_strong, (*set_transfer,*) rel_Grp, rel_conversep,
          rel_OO, rel_refl, rel_refl_strong, rel_reflp, rel_symp, rel_transp, rel_transfer, rel_eq_onp,
          pred_transfer, pred_True, pred_map, pred_rel, pred_mono_strong0, pred_mono_strong, pred_mono,
          pred_cong0, pred_cong, pred_cong_simp];*)
      in
        note_mrbnf_thms fact_policy qualify mrbnf_b mrbnf lthy
      end;

    val one_step_defs =
      no_reflexive (mrbnf_map_def :: mrbnf_bd_def :: mrbnf_set_defs @ mrbnf_wit_defs @
        [mrbnf_rel_def, mrbnf_pred_def]);
  in
    (key, goals, wit_goalss, after_qed, lthy, one_step_defs)
  end;

structure MRBNF_Plugin = Plugin(type T = mrbnf);

fun mrbnf_interpretation name f =
  MRBNF_Plugin.interpretation name
    (fn mrbnf => fn lthy => f (transfer_mrbnf (Proof_Context.theory_of lthy) mrbnf) lthy);

val interpret_mrbnf = MRBNF_Plugin.data;

fun register_mrbnf_raw key mrbnf =
  Local_Theory.declaration {syntax = false, pos = Position.none, pervasive = true}
    (fn phi => Data.map (Symtab.update (key, morph_mrbnf phi mrbnf)));

fun register_mrbnf plugins key mrbnf =
  register_mrbnf_raw key mrbnf #> interpret_mrbnf plugins mrbnf;

type mrbnf_def_tactics = {
  map_id0: Proof.context -> tactic,
  map_comp0: Proof.context -> tactic,
  map_cong0: Proof.context -> tactic,
  set_map0: (Proof.context -> tactic) list,
  infinite_regular_card_order: Proof.context -> tactic,
  set_bd: (Proof.context -> tactic) list,
  le_rel_OO: Proof.context -> tactic,
  in_rel: Proof.context -> tactic,
  pred_set: Proof.context -> tactic,
  wit: Proof.context -> tactic
}

fun mrbnf_def const_policy fact_policy internal qualify tacs Ds classes
    map_b rel_b pred_b set_bs raw_csts =
  (fn (_, goals, (triv_tac_opt, wit_goalss), after_qed, lthy, one_step_defs) =>
  let
    fun mk_wits_tac ctxt set_maps =
      assume_tac ctxt 1 ORELSE
      (TRYALL Goal.conjunction_tac THEN
      (case triv_tac_opt of
        SOME tac => tac ctxt set_maps
      | NONE => unfold_thms_tac ctxt one_step_defs THEN (#wit tacs) ctxt));
    val wit_goals = map Logic.mk_conjunction_balanced wit_goalss;
    fun mk_wit_thms set_maps =
      Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced wit_goals)
        (fn {context = ctxt, prems = _} => mk_wits_tac ctxt set_maps)
        |> Thm.close_derivation \<^here>
        |> Conjunction.elim_balanced (length wit_goals)
        |> map2 (Conjunction.elim_balanced o length) wit_goalss
        |> (map o map) (Thm.forall_elim_vars 0);
    val tac_list = [#map_id0 tacs, #map_comp0 tacs, #map_cong0 tacs]
      @ #set_map0 tacs @ [#infinite_regular_card_order tacs] @ #set_bd tacs
      @ [#le_rel_OO tacs, #in_rel tacs, #pred_set tacs]
  in
    map2 (Thm.close_derivation \<^here> oo Goal.prove_sorry lthy [] [])
      goals (map (fn tac => fn {context = ctxt, prems = _} =>
        unfold_thms_tac ctxt one_step_defs THEN tac ctxt) tac_list)
    |> (fn thms => after_qed mk_wit_thms (map single thms) lthy)
  end) o prepare_def const_policy fact_policy internal qualify (K I) (K I) (K I) Ds classes
    map_b rel_b pred_b set_bs (raw_csts, NONE);

fun mrbnf_of_bnf bnf lthy =
  let val mrbnf_tactics = {
    map_id0 = fn ctxt => HEADGOAL (resolve_tac ctxt [BNF_Def.map_id0_of_bnf bnf]),
    map_comp0 = fn ctxt => HEADGOAL (resolve_tac ctxt [BNF_Def.map_comp0_of_bnf bnf]),
    map_cong0 = fn ctxt => HEADGOAL (SUBGOAL (K (HEADGOAL (resolve_tac ctxt [BNF_Def.map_cong0_of_bnf bnf]) THEN REPEAT (Goal.assume_rule_tac ctxt 1)))),
    set_map0 = map (fn thm => fn ctxt => HEADGOAL (resolve_tac ctxt [thm])) (BNF_Def.set_map0_of_bnf bnf),
    infinite_regular_card_order = fn ctxt => rtac ctxt (@{thm infinite_regular_card_order.intro} OF [
      BNF_Def.bd_card_order_of_bnf bnf,
      BNF_Def.bd_cinfinite_of_bnf bnf,
      BNF_Def.bd_regularCard_of_bnf bnf
    ]) 1,
    set_bd = map (fn thm => fn ctxt => rtac ctxt thm 1) (BNF_Def.set_bd_of_bnf bnf),
    le_rel_OO = fn ctxt => HEADGOAL (resolve_tac ctxt [BNF_Def.le_rel_OO_of_bnf bnf]),
    in_rel = fn ctxt => Local_Defs.unfold_tac ctxt [@{thm OO_Grp_alt}, BNF_Def.map_id_of_bnf bnf] THEN FIRST [
        HEADGOAL (resolve_tac ctxt [@{thm exists_univ_eq}]),
        Local_Defs.unfold_tac ctxt [BNF_Def.in_rel_of_bnf bnf, @{thm Set.mem_Collect_eq}] THEN HEADGOAL (resolve_tac ctxt [@{thm refl}])
      ],
    pred_set = fn ctxt => HEADGOAL (resolve_tac ctxt [BNF_Def.pred_set_of_bnf bnf]),
    wit = fn ctxt => FIRST [
        HEADGOAL (assume_tac ctxt),
        EVERY (map (HEADGOAL o eresolve_tac ctxt o single) (BNF_Def.wit_thms_of_bnf bnf))
      ]
  }
  val n = BNF_Def.live_of_bnf bnf
  val nwits = BNF_Def.nwits_of_bnf bnf
  val (((lives, lives'), deads), _) = lthy
    |> Ctr_Sugar_Util.mk_TFrees n
    ||>> Ctr_Sugar_Util.mk_TFrees n
    ||>> Ctr_Sugar_Util.mk_TFrees' (map Type.sort_of_atyp (BNF_Def.deads_of_bnf bnf))
  in mrbnf_def Do_Inline (K Dont_Note) false I mrbnf_tactics (SOME deads) NONE
      Binding.empty Binding.empty Binding.empty []
    (((((((BNF_Def.name_of_bnf bnf, BNF_Def.mk_T_of_bnf deads lives bnf), BNF_Def.mk_map_of_bnf deads lives lives' bnf),
    map (fn x => (Live_Var, x)) (BNF_Def.mk_sets_of_bnf (replicate n deads) (replicate n lives) bnf)),
    BNF_Def.mk_bd_of_bnf deads lives bnf),
    map snd (BNF_Def.mk_wits_of_bnf (replicate nwits deads) (replicate nwits lives) bnf)),
    SOME (BNF_Def.mk_rel_of_bnf deads lives lives' bnf)),
    SOME (BNF_Def.mk_pred_of_bnf deads lives bnf))
    lthy
  end;

fun register_bnf_as_mrbnf key bnf lthy =
  let val (mrbnf, lthy') = mrbnf_of_bnf bnf lthy
      val name = (case key of
        SOME name => name
        | NONE => fst (dest_Type (BNF_Def.T_of_bnf bnf))
      )
      val lthy'' = register_mrbnf_raw name mrbnf lthy'
  in (mrbnf, lthy'')
  end;

fun bnf_of_mrbnf mrbnf lthy =
  if live_of_mrbnf mrbnf = 0 then (NONE, lthy) else
  let
    val var_types = var_types_of_mrbnf mrbnf;
    fun map_filter_live f xs = map_filter (fn (Live_Var, x) => SOME (f x) | (_, _) => NONE) (var_types ~~ xs);

    val n = live_of_mrbnf mrbnf
    val free = free_of_mrbnf mrbnf;
    val bound = bound_of_mrbnf mrbnf;
    val id_prems = maps (fn Bound_Var => @{thms bij_id supp_id_bound} | Free_Var => @{thms supp_id_bound} | _ => []) var_types
    val o_id = Local_Defs.unfold0 lthy @{thms o_id}

    fun map_id0_tac ctxt = rtac ctxt (map_id0_of_mrbnf mrbnf) 1;
    fun map_comp0_tac ctxt = rtac ctxt (o_id (map_comp0_of_mrbnf mrbnf OF (id_prems @ id_prems))) 1;
    fun map_cong0_tac ctxt = rtac ctxt (map_cong0_of_mrbnf mrbnf OF (id_prems @ id_prems)) 1 THEN
      REPEAT_DETERM (HEADGOAL (rtac ctxt refl ORELSE' Goal.assume_rule_tac ctxt));
    val set_map0_tacs = map_filter_live (fn thm => fn ctxt => rtac ctxt (thm OF id_prems) 1) (
      set_map0_of_mrbnf mrbnf
    );
    fun bd_card_order_tac ctxt = rtac ctxt (@{thm infinite_regular_card_order.card_order} OF [
      bd_infinite_regular_card_order_of_mrbnf mrbnf
    ]) 1;
    fun bd_cinfinite_tac ctxt = rtac ctxt (@{thm infinite_regular_card_order.cinfinite} OF [
      bd_infinite_regular_card_order_of_mrbnf mrbnf
    ]) 1;
    fun bd_regular_tac ctxt = rtac ctxt (@{thm infinite_regular_card_order.regularCard} OF [
      bd_infinite_regular_card_order_of_mrbnf mrbnf
    ]) 1;
    val set_bd_tacs = map_filter_live (fn thm => fn ctxt => rtac ctxt thm 1) (
      set_bd_of_mrbnf mrbnf
    );
    fun le_rel_OO_tac ctxt = rtac ctxt (le_rel_OO_of_mrbnf mrbnf) 1;
    fun rel_OO_Grp_tac ctxt = rtac ctxt (Ctr_Sugar_Util.mk_unabs_def n @{thm meta_eq_to_obj_eq} OF
      [Local_Defs.abs_def_rule lthy (Local_Defs.unfold0 lthy [map_id_of_mrbnf mrbnf] (rel_OO_Grp_of_mrbnf mrbnf OF id_prems))]) 1;
    fun pred_set_tac ctxt = rtac ctxt (pred_set_of_mrbnf mrbnf) 1;

    val tacs = BNF_Def.zip_axioms map_id0_tac map_comp0_tac map_cong0_tac set_map0_tacs bd_card_order_tac
      bd_cinfinite_tac bd_regular_tac set_bd_tacs le_rel_OO_tac rel_OO_Grp_tac pred_set_tac;
    fun wit_tac ctxt = EVERY1 (map (fn thm => rtac ctxt thm THEN' assume_tac ctxt) (wit_thms_of_mrbnf mrbnf));

    val nwits = nwits_of_mrbnf mrbnf
    val (((((lives, lives'), frees), bounds), deads), lthy') = lthy
      |> Ctr_Sugar_Util.mk_TFrees n
      ||>> Ctr_Sugar_Util.mk_TFrees n
      ||>> Ctr_Sugar_Util.mk_TFrees' (map Type.sort_of_atyp (frees_of_mrbnf mrbnf))
      ||>> Ctr_Sugar_Util.mk_TFrees' (map Type.sort_of_atyp (bounds_of_mrbnf mrbnf))
      ||>> Ctr_Sugar_Util.mk_TFrees' (map Type.sort_of_atyp (deads_of_mrbnf mrbnf))

    val count = n + free + bound;
    val is_live = map (fn Live_Var => true | _ => false) var_types
    val sets = mk_sets_of_mrbnf (replicate count deads) (replicate count lives)
      (replicate count bounds) (replicate count frees)  mrbnf
    val live_sets = cond_keep sets is_live
    val ABF_types = map (HOLogic.dest_setT o range_type o fastype_of) sets;
    val ids = map HOLogic.id_const (cond_keep ABF_types (map not is_live));
    val mapx = fold_rev Term.absdummy (map2 (curry op-->) lives lives') (Term.list_comb (
      mk_map_of_mrbnf deads lives lives' bounds frees mrbnf, cond_interlace (map Bound (n - 1 downto 0)) ids is_live
    ));
  in
    apfst SOME (BNF_Def.bnf_def BNF_Def.Do_Inline (K BNF_Def.Dont_Note) false I tacs wit_tac (SOME (frees @ bounds @ deads)) Binding.empty
      Binding.empty Binding.empty [] (((((((name_of_mrbnf mrbnf, mk_T_of_mrbnf deads lives bounds frees mrbnf),
      mapx), live_sets), mk_bd_of_mrbnf deads bounds frees mrbnf), map snd (
        mk_wits_of_mrbnf (replicate nwits deads) (replicate nwits lives) (replicate nwits bounds) (replicate nwits frees) mrbnf)),
      SOME (mk_rel_of_mrbnf deads lives lives' bounds frees mrbnf)),
      SOME (mk_pred_of_mrbnf deads lives bounds frees mrbnf)) lthy')
  end;

fun register_mrbnf_as_bnf mrbnf lthy =
  let val (bnf_opt, lthy') = bnf_of_mrbnf mrbnf lthy
      val name = fst (dest_Type (T_of_mrbnf mrbnf))
      val lthy'' = case bnf_opt of
        SOME bnf => BNF_Def.register_bnf_raw name bnf lthy'
        | _ => lthy';
  in (bnf_opt, lthy'') end

fun as_mrbnf name lthy' =
  (case mrbnf_of lthy' name of
    SOME mrbnf => SOME (mrbnf, lthy')
    | NONE =>
      (case BNF_Def.bnf_of lthy' name of
        SOME bnf => SOME (register_bnf_as_mrbnf NONE bnf lthy')
        | NONE => NONE
      )
  )

fun mrbnf_cmd (raw_csts, raw_plugins) =
  (fn (key, goals, (triv_tac_opt, wit_goalss), after_qed, lthy, defs) =>
  let
    val plugins = raw_plugins lthy;
    val wit_goals = map Logic.mk_conjunction_balanced wit_goalss;
    fun mk_triv_wit_thms tac set_maps =
      Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced wit_goals)
        (fn {context = ctxt, prems = _} => TRYALL Goal.conjunction_tac THEN tac ctxt set_maps)
        |> Thm.close_derivation \<^here>
        |> Conjunction.elim_balanced (length wit_goals)
        |> map2 (Conjunction.elim_balanced o length) wit_goalss
        |> (map o map) (Thm.forall_elim_vars 0);
    val (mk_wit_thms, nontriv_wit_goals) =
      (case triv_tac_opt of
        NONE => (fn _ => [], map (map (rpair [])) wit_goalss)
      | SOME tac => (mk_triv_wit_thms tac, []));
  in
    lthy
    |> Proof.theorem NONE (fn thmss => fn lthy =>
      let
        val (mrbnf, lthy) = after_qed mk_wit_thms thmss lthy;
        val lthy = register_mrbnf plugins key mrbnf lthy;
        val (bnf_opt, lthy) = case BNF_Def.bnf_of lthy key of
          SOME _ => (NONE, lthy)
          | NONE => bnf_of_mrbnf mrbnf lthy;
        val lthy = case bnf_opt of
          NONE => lthy
          | SOME bnf => BNF_Def.register_bnf plugins key bnf lthy
      in lthy end
    ) (map (single o rpair []) goals @ nontriv_wit_goals)
    |> Proof.unfolding ([[(@{thm OO_Grp_alt} :: @{thm mem_Collect_eq} :: defs, [])]])
    |> Proof.refine_singleton (Method.Basic (fn ctxt =>
      Method.SIMPLE_METHOD (TRYALL (rtac ctxt refl))))
  end) o prepare_def Do_Inline (user_policy Note_Some) false I Syntax.read_typ Syntax.read_term Syntax.read_sort
    NONE NONE Binding.empty Binding.empty Binding.empty [] raw_csts;

fun print_mrbnfs ctxt =
  let
    fun pretty_set sets i = Pretty.block
      [Pretty.str (mk_setN (i + 1) ^ ":"), Pretty.brk 1,
        Pretty.quote (Syntax.pretty_term ctxt (nth sets i))];

    fun pretty_mrbnf (key, MRBNF {T, map, sets, bd, live, lives, bound, bounds, free, frees,
        dead, deads, ...}) =
      Pretty.big_list
        (Pretty.string_of (Pretty.block [Pretty.str key, Pretty.str ":", Pretty.brk 1,
          Pretty.quote (Syntax.pretty_typ ctxt T)]))
        ([Pretty.block [Pretty.str "live:", Pretty.brk 1, Pretty.str (string_of_int live),
            Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) lives)]] @
          (if bound > 0 then
            [Pretty.block [Pretty.str "bound:", Pretty.brk 1, Pretty.str (string_of_int bound),
              Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) bounds)]]
          else []) @
          (if free > 0 then
            [Pretty.block [Pretty.str "free:", Pretty.brk 1, Pretty.str (string_of_int free),
              Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) frees)]]
            else []) @
          [Pretty.block [Pretty.str "dead:", Pretty.brk 1, Pretty.str (string_of_int dead),
            Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) deads)],
          Pretty.block [Pretty.str (mapN ^ ":"), Pretty.brk 1,
            Pretty.quote (Syntax.pretty_term ctxt map)]] @
          List.map (pretty_set sets) (0 upto length sets - 1) @
          [Pretty.block [Pretty.str (bdN ^ ":"), Pretty.brk 1,
            Pretty.quote (Syntax.pretty_term ctxt bd)]]);
  in
    Pretty.big_list "Registered map restricted bounded natural functors:"
      (map pretty_mrbnf (sort_by fst (Symtab.dest (Data.get (Context.Proof ctxt)))))
    |> Pretty.writeln
  end;

val _ =
  Outer_Syntax.command @{command_keyword print_mrbnfs}
    "print all bounded natural functors"
    (Scan.succeed (Toplevel.keep (print_mrbnfs o Toplevel.context_of)));

val parse_var_type =
  Parse.reserved "free" -- @{keyword ":"} >> K Free_Var
  || Parse.reserved "bound" -- @{keyword ":"} >> K Bound_Var
  || Parse.reserved "live" -- @{keyword ":"} >> K Live_Var
  || Scan.succeed Live_Var;

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword mrbnf}
    "register a type as a bounded natural functor"
    (parse_opt_binding_colon -- Parse.typ --|
       (Parse.reserved "map" -- @{keyword ":"}) -- Parse.term --
       (Scan.optional ((Parse.reserved "sets" -- @{keyword ":"}) |--
         Scan.repeat1 (Scan.unless (Parse.reserved "bd") (parse_var_type -- Parse.term))) []) --|
       (Parse.reserved "bd" -- @{keyword ":"}) -- Parse.term --
       Scan.optional ((Parse.reserved "wits" -- @{keyword ":"}) |--
         Scan.repeat1 (Scan.unless (Parse.reserved "rel" || Parse.reserved "pred" || Parse.reserved "var_class" || 
           Parse.reserved "plugins") Parse.term)) [] --
       Scan.option ((Parse.reserved "rel" -- @{keyword ":"}) |-- Parse.term) --
       Scan.option ((Parse.reserved "pred" -- @{keyword ":"}) |-- Parse.term) --
       Scan.option ((Parse.reserved "var_class" -- @{keyword ":"}) |-- Parse.sort) --
       Scan.optional Plugin_Name.parse_filter (K Plugin_Name.default_filter)
       >> mrbnf_cmd);

end;
