(*  Title:      HOL/Tools/BNF/bnf_comp.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012
Composition of bounded natural functors.
*)

signature MRBNF_COMP =
sig
  val typedef_threshold: int Config.T
  val with_typedef_threshold: int -> (Proof.context -> Proof.context) -> Proof.context ->
    Proof.context
  val with_typedef_threshold_yield: int -> (Proof.context -> 'a * Proof.context) -> Proof.context ->
    'a * Proof.context

  val as_mrbnf: string -> local_theory -> (MRBNF_Def.mrbnf * local_theory) option

  val ID_mrbnf: MRBNF_Def.mrbnf
  val DEADID_mrbnf: MRBNF_Def.mrbnf

  type comp_cache
  type unfold_set =
    {map_unfolds: thm list,
     set_unfoldss: thm list list,
     rel_unfolds: thm list}

  val empty_comp_cache: comp_cache
  val empty_unfolds: unfold_set

(*
  exception BAD_DEAD of typ * typ
*)
  (*val mrbnf_of_typ: bool -> MRBNF_Def.inline_policy -> (binding -> binding) ->
    ((string * sort) list list -> (string * sort) list) -> (string * sort) list ->
    (string * sort) list -> typ -> (comp_cache * unfold_set) * local_theory ->
    (MRBNF_Def.mrbnf * (typ list * typ list)) * ((comp_cache * unfold_set) * local_theory)
  val default_comp_sort: (string * sort) list list -> (string * sort) list*)
  val clean_compose_mrbnf: MRBNF_Def.inline_policy -> (binding -> binding) -> binding -> MRBNF_Def.mrbnf ->
    MRBNF_Def.mrbnf list -> unfold_set * local_theory -> MRBNF_Def.mrbnf * (unfold_set * local_theory)
  val multi_kill_mrbnf: (binding -> binding) -> MRBNF_Def.var_type list -> MRBNF_Def.mrbnf ->
    (comp_cache * unfold_set) * local_theory ->
    MRBNF_Def.mrbnf * ((comp_cache * unfold_set) * local_theory)
  val multilift_mrbnf: (binding -> binding) -> int -> int -> int -> MRBNF_Def.mrbnf ->
    (comp_cache * unfold_set) * local_theory ->
    MRBNF_Def.mrbnf * ((comp_cache * unfold_set) * local_theory)
  val permute_mrbnf: (binding -> binding) -> int list -> int list -> MRBNF_Def.mrbnf ->
    (comp_cache * unfold_set) * local_theory ->
    MRBNF_Def.mrbnf * ((comp_cache * unfold_set) * local_theory)
(*  val permute_and_kill_mrbnf: (binding -> binding) -> int -> int list -> int list -> MRBNF_Def.mrbnf ->
    (comp_cache * unfold_set) * local_theory ->
    MRBNF_Def.mrbnf * ((comp_cache * unfold_set) * local_theory)
  val lift_and_permute_mrbnf: (binding -> binding) -> int -> int list -> int list -> MRBNF_Def.mrbnf ->
    (comp_cache * unfold_set) * local_theory ->
    MRBNF_Def.mrbnf * ((comp_cache * unfold_set) * local_theory)
  val normalize_mrbnfs: (int -> binding -> binding) -> ''a list list -> ''a list ->
    (''a list list -> ''a list) -> MRBNF_Def.mrbnf list -> (comp_cache * unfold_set) * local_theory ->
    (int list list * ''a list) * (MRBNF_Def.mrbnf list * ((comp_cache * unfold_set) * local_theory))
  val compose_mrbnf: MRBNF_Def.inline_policy -> (int -> binding -> binding) ->
    ((string * sort) list list -> (string * sort) list) -> MRBNF_Def.mrbnf -> MRBNF_Def.mrbnf list ->
    typ list -> typ list list -> typ list list -> (comp_cache * unfold_set) * local_theory ->
    (MRBNF_Def.mrbnf * (typ list * typ list)) * ((comp_cache * unfold_set) * local_theory)
  type absT_info =
    {absT: typ,
     repT: typ,
     abs: term,
     rep: term,
     abs_inject: thm,
     abs_inverse: thm,
     type_definition: thm}
  val morph_absT_info: morphism -> absT_info -> absT_info
  val mk_absT: theory -> typ -> typ -> typ -> typ
  val mk_repT: typ -> typ -> typ -> typ
  val mk_abs: typ -> term -> term
  val mk_rep: typ -> term -> term
  val seal_mrbnf: (binding -> binding) -> unfold_set -> binding -> bool -> typ list -> typ list ->
    MRBNF_Def.mrbnf -> local_theory -> (MRBNF_Def.mrbnf * (typ list * absT_info)) * local_theory*)
end;

structure MRBNF_Comp : MRBNF_COMP =
struct

open MRBNF_Def
open BNF_Util
open MRBNF_Util
open BNF_Tactics
open BNF_Comp_Tactics
open MRBNF_Comp_Tactics

val typedef_threshold = Attrib.setup_config_int @{binding mrbnf_typedef_threshold} (K 6);

fun with_typedef_threshold threshold f lthy =
  lthy
  |> Config.put typedef_threshold threshold
  |> f
  |> Config.put typedef_threshold (Config.get lthy typedef_threshold);

fun with_typedef_threshold_yield threshold f lthy =
  lthy
  |> Config.put typedef_threshold threshold
  |> f
  ||> Config.put typedef_threshold (Config.get lthy typedef_threshold);

val ID_mrbnf = the (mrbnf_of \<^context> "BNF_Composition.ID");
val DEADID_mrbnf = the (mrbnf_of \<^context> "BNF_Composition.DEADID");

type comp_cache = (mrbnf * (typ list * typ list)) Typtab.table;

fun key_of_types s Ts = Type (s, Ts);
fun key_of_typess s = key_of_types s o map (key_of_types "");
fun typ_of_int n = Type (string_of_int n, []);
fun typ_of_mrbnf mrbnf =
  key_of_typess "" [[T_of_mrbnf mrbnf], lives_of_mrbnf mrbnf, sort Term_Ord.typ_ord (deads_of_mrbnf mrbnf)];

fun key_of_kill n mrbnf = key_of_types "k" [typ_of_int n, typ_of_mrbnf mrbnf];
fun key_of_lift n mrbnf = key_of_types "l" [typ_of_int n, typ_of_mrbnf mrbnf];
fun key_of_multilift n m l mrbnf = key_of_types "l+" [typ_of_int n, typ_of_int m, typ_of_int l, typ_of_mrbnf mrbnf];

fun key_of_permute src dest mrbnf =
  key_of_types "p" (map typ_of_int src @ map typ_of_int dest @ [typ_of_mrbnf mrbnf]);
fun key_of_compose oDs Dss Ass outer inners =
  key_of_types "c" (map (key_of_typess "") [[oDs], Dss, Ass, [map typ_of_mrbnf (outer :: inners)]]);

fun cache_comp_simple key cache (mrbnf, (unfold_set, lthy)) =
  (mrbnf, ((Typtab.update (key, (mrbnf, ([], []))) cache, unfold_set), lthy));

fun cache_comp key (mrbnf_Ds_As, ((cache, unfold_set), lthy)) =
  (mrbnf_Ds_As, ((Typtab.update (key, mrbnf_Ds_As) cache, unfold_set), lthy));

type unfold_set = {
  map_unfolds: thm list,
  set_unfoldss: thm list list,
  rel_unfolds: thm list
};

fun as_mrbnf name lthy' =
  (case mrbnf_of lthy' name of
    SOME mrbnf => SOME (mrbnf, lthy')
    | NONE =>
      (case BNF_Def.bnf_of lthy' name of
        SOME bnf => SOME (register_bnf_as_mrbnf NONE bnf lthy')
        | NONE => NONE
      )
  )

val empty_comp_cache = Typtab.empty;
val empty_unfolds = {map_unfolds = [], set_unfoldss = [], rel_unfolds = []};

fun add_to_thms thms new = thms |> not (Thm.is_reflexive new) ? insert Thm.eq_thm new;
fun adds_to_thms thms news = insert (eq_set Thm.eq_thm) (no_reflexive news) thms;

fun add_to_unfolds map sets rel
  {map_unfolds, set_unfoldss, rel_unfolds} =
  {map_unfolds = add_to_thms map_unfolds map,
    set_unfoldss = adds_to_thms set_unfoldss sets,
    rel_unfolds = add_to_thms rel_unfolds rel};

fun add_mrbnf_to_unfolds mrbnf =
  add_to_unfolds (map_def_of_mrbnf mrbnf) (set_defs_of_mrbnf mrbnf) (rel_def_of_mrbnf mrbnf);

val bdTN = "bdT";

fun mk_killN n = "_kill" ^ string_of_int n;
fun mk_liftN n = "_lift" ^ string_of_int n;
fun mk_permuteN src dest =
  "_permute_" ^ implode (map string_of_int src) ^ "_" ^ implode (map string_of_int dest);


(*copied from Envir.expand_term_free*)
fun expand_term_const defs =
  let
    val eqs = map ((fn ((x, U), u) => (x, (U, u))) o apfst dest_Const) defs;
    val get = fn Const (x, _) => AList.lookup (op =) eqs x | _ => NONE;
  in Envir.expand_term get end;

val id_mrbnf_def = @{thm BNF_Composition.id_bnf_def};
val expand_id_mrbnf_def = expand_term_const [Thm.prop_of id_mrbnf_def |> Logic.dest_equals];

fun is_sum_prod_natLeq (Const (@{const_name BNF_Cardinal_Arithmetic.csum}, _) $ t $ u) = forall is_sum_prod_natLeq [t, u]
  | is_sum_prod_natLeq (Const (@{const_name BNF_Cardinal_Arithmetic.cprod}, _) $ t $ u) = forall is_sum_prod_natLeq [t, u]
  | is_sum_prod_natLeq t = t aconv @{term natLeq};

(*
 * Instantiates the live variables of an outer MRBNF with several inner MRBNFs and returns a composed MRBNF.
 * The composed MRBNF will have:
 *   - The union of the dead variables of the outer and the inner MRBNFs
 *   - The live variables of the inner MRBNFs (which are the same for all inner MRBNFs by invariant)
 *   - The free and bound variables of the outer MRBNF (which are the same as those of all inner MRBNFs by invariant)
 *
 * INVARIANTS:
 *   - All inner MRBNFs have the same live variables in the same order
 *   - Outer and all inner MRBNFs have the same bound and free variables in the same order (the live variables are ignored while checking the order)
 *   - There are as many inner MRBNFs as there are live variables on the outer MRBNF
 *)
fun clean_compose_mrbnf const_policy qualify binding outer inners (unfold_set, lthy) =
  let
    val num_ilives = live_of_mrbnf (hd inners);
    val num_free = free_of_mrbnf outer;
    val num_bound = bound_of_mrbnf outer;
    val num_inondead = num_ilives + num_free + num_bound;
    val num_onondead = live_of_mrbnf outer + num_free + num_bound;
    val ivar_types = var_types_of_mrbnf (hd inners);
    val is_ilive = map (equal Live_Var) ivar_types;
    val is_olive = map (equal Live_Var) (var_types_of_mrbnf outer);

    fun interlace _ _ _ [] = []
      | interlace (a :: als) bs fs (Live_Var::ts) = a :: interlace als bs fs ts
      | interlace als (b::bs) fs (Bound_Var::ts) = b :: interlace als bs fs ts
      | interlace als bs (f::fs) (Free_Var::ts) = f :: interlace als bs fs ts

    (* Combine variable type classes of outer and inners into a single sort *)
    val sort = fold (curry (Sign.inter_sort (Proof_Context.theory_of lthy))) (map class_of_mrbnf inners) (class_of_mrbnf outer);
    val cosort = fold (curry (Sign.inter_sort (Proof_Context.theory_of lthy))) (map coclass_of_mrbnf inners) (coclass_of_mrbnf outer);

    (* Invent variable names for deads of outer and inner *)
    val (oDs, lthy1) = apfst (map TFree) (Variable.invent_types (map Type.sort_of_atyp (deads_of_mrbnf outer)) lthy);
    val (iDss, lthy2) = apfst (map (map TFree)) (fold_map Variable.invent_types (map (map Type.sort_of_atyp) (map deads_of_mrbnf inners)) lthy1);

    (* Invent variable names for bounds and frees (by invariant the same on outer and all inners) *)
    val (Fs, lthy3) = apfst (map TFree) (Variable.invent_types (map (K sort) (frees_of_mrbnf outer)) lthy2);
    val (Bs, lthy4) = apfst (map TFree) (Variable.invent_types (map (K sort) (bounds_of_mrbnf outer)) lthy3);

    (* Invent variable names for lives of inners (by invariant all inners have the same lives)
     * Live variables of outer are instantiated by the composition, so no variables names are needed.
     * The code invents two lists of names because of map: e.g. for "('a \<rightarrow> 'b) \<rightarrow> 'a F \<rightarrow> 'b F" As = ['a] and As' = ['b]
     * names_lthy is the local context after new variable names have been invented *)
    val (As, lthy5) = apfst (map TFree) (Variable.invent_types (replicate num_ilives @{sort type}) lthy4);
    val (As', names_lthy) = apfst (map TFree) (Variable.invent_types (replicate num_ilives @{sort type}) lthy5);

    (* Create the types of the inners, the only thing that is not the same by invariant are the dead variables.
     * This is dones once for the As and once for the As' of the live variables *)
    val iTs = map2 (fn deads => mk_T_of_mrbnf deads As Bs Fs) iDss inners;
    val iTs' = map2 (fn deads => mk_T_of_mrbnf deads As' Bs Fs) iDss inners;

    (* Create the type of the outer, this will replace the live variables of the outer with the types of the inners *)
    val oT = mk_T_of_mrbnf oDs iTs Bs Fs outer;

    (* Create the composed bound (bd) for the new MRBNF: bd = (inner_1.bd +c inner_2.bd +c ... +c inner_m.bd) *c outer.bd *)
    val bd = BNF_Util.mk_cprod (foldr1 (uncurry BNF_Util.mk_csum) (map bd_of_mrbnf inners)) (bd_of_mrbnf outer)

    (* In case the composed bound only consists of sums and products of "natLeq", simplify the bound to just "natLeq" *)
    val (bd', bd_ordIso_natLeq_thm_opt) =
      if is_sum_prod_natLeq bd then
        let
          val bd' = @{term natLeq};
          val bd_bd' = HOLogic.mk_prod (bd, bd');
          val ordIso = Const (@{const_name ordIso}, HOLogic.mk_setT (fastype_of bd_bd'));
          val goal = BNF_Util.mk_Trueprop_mem (bd_bd', ordIso)
        in (bd', SOME (Goal.prove_sorry lthy [] [] goal (BNF_Comp_Tactics.bd_ordIso_natLeq_tac o #context) |> Thm.close_derivation \<^here>))
        end
      else (bd, NONE);

    fun map_id0_tac ctxt =
      mr_mk_comp_map_id0_tac ctxt (map_id0_of_mrbnf outer) (map_cong0_of_mrbnf outer) (map map_id0_of_mrbnf inners);

    fun map_comp0_tac ctxt =
      mr_mk_comp_map_comp0_tac ctxt (map_comp0_of_mrbnf outer) (map_cong0_of_mrbnf outer) (map map_comp0_of_mrbnf inners) outer;

    fun bd_infinite_regular_card_order_tac ctxt =
      mr_mk_comp_bd_card_order_tac ctxt (map bd_card_order_of_mrbnf inners) (bd_card_order_of_mrbnf outer);

    val outer_sets = mk_sets_of_mrbnf (replicate num_onondead oDs) (replicate num_onondead iTs)
      (replicate num_onondead Bs) (replicate num_onondead Fs) outer;
    val inner_setss = map2 (fn Ds => mk_sets_of_mrbnf (replicate num_inondead Ds)
      (replicate num_inondead As) (replicate num_inondead Bs) (replicate num_inondead Fs))
      iDss inners;
    val (sets, sets_alt) =
      let
        val ovar_types = var_types_of_mrbnf outer;
        val ivars = ivar_types ~~ interlace As Bs Fs ivar_types;

        fun mk_set (i, (var_type, T)) =
          let
            val setTs = replicate (live_of_mrbnf outer) (HOLogic.mk_setT T);
            fun filter_olives xs = map fst (filter (equal Live_Var o snd) (xs ~~ ovar_types));
            fun mk_olive_sets Ts = filter_olives (mk_sets_of_mrbnf (replicate num_onondead oDs)
                (replicate num_onondead Ts) (replicate num_onondead Bs) (replicate num_onondead Fs) outer);
            val ilive_sets = map (fn sets => nth sets i) inner_setss;

            val map_inner_sets = Term.list_comb (
              mk_map_of_mrbnf oDs iTs setTs Bs Fs outer,
              interlace ilive_sets (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) ovar_types
            );
            val collect_map = mk_collect (mk_olive_sets setTs) (mk_T_of_mrbnf oDs setTs Bs Fs outer --> HOLogic.mk_setT T);
            val union_map = mk_Union T $ (collect_map $ (map_inner_sets $ Bound 0));

            val compose_inner_sets = map (fn (oset, iset) => HOLogic.mk_comp (mk_image iset, oset)) (mk_olive_sets iTs ~~ ilive_sets)
            val collect_compose = mk_collect compose_inner_sets (oT --> HOLogic.mk_setT T)
            val union_compose = HOLogic.mk_comp (mk_Union T, collect_compose) $ Bound 0

            fun aux_mk_set u = Term.absdummy oT (case var_type of
              Live_Var => u
              | _ => mk_union (nth outer_sets i $ Bound 0, u)
            ) |> Syntax.check_term names_lthy;
          in (aux_mk_set union_map, aux_mk_set union_compose) end;
      in map_split mk_set (0 upto num_inondead - 1 ~~ ivars) end;

    fun mk_simplified_set set =
      let
        val setT = fastype_of set;
        val var_set' = Const (@{const_name BNF_Composition.id_bnf}, setT --> setT) $ Var ((Name.uu, 0), setT);
        val goal = mk_Trueprop_eq (var_set', set);
        fun tac {context = ctxt, prems = _} =
          mk_simplified_set_tac ctxt (collect_set_map_of_mrbnf outer);
        val set'_eq_set =
          Goal.prove names_lthy [] [] goal tac
          |> Thm.close_derivation \<^here>;
        val set' = fst (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of set'_eq_set)));
      in
        (set', set'_eq_set)
      end;

    val (sets', set'_eq_sets) =
      map_split mk_simplified_set sets
      ||> Proof_Context.export names_lthy lthy;

    fun mk_single_set_map0_tac i ctxt =
      mr_mk_comp_set_map0_tac ctxt (nth set'_eq_sets i) (map_comp0_of_mrbnf outer)
        (map_cong0_of_mrbnf outer) (collect_set_map_of_mrbnf outer)
        (map ((fn thms => nth thms i) o set_map0_of_mrbnf) inners);

    val set_map0_tacs = map mk_single_set_map0_tac (0 upto num_inondead - 1);

    fun mr_mk_comp_set_alt_tac ctxt collect_set_map =
      rtac ctxt (fun_cong) 1 THEN
      unfold_thms_tac ctxt (@{thms comp_assoc}) THEN
      unfold_thms_tac ctxt [(collect_set_map RS sym)] THEN
      Skip_Proof.cheat_tac ctxt 1;

    val set_alt_thms =
      if Config.get lthy quick_and_dirty then
        []
      else
        map (fn goal =>
          Goal.prove_sorry lthy [] [] goal
            (fn {context = ctxt, prems = _} =>
              mr_mk_comp_set_alt_tac ctxt (collect_set_map_of_mrbnf outer))
          |> Thm.close_derivation \<^here> )
        (map2 (curry mk_Trueprop_eq) sets sets_alt)
          |> (fn thms => cond_automap (fn thm => thm RS fun_cong) thms is_ilive);

    fun map_cong0_tac ctxt =
      mr_mk_comp_map_cong0_tac ctxt set'_eq_sets set_alt_thms (map map_cong0_of_mrbnf inners)
        outer ivar_types

    val set_bd_tacs =
      if Config.get lthy quick_and_dirty then
        replicate num_ilives (K all_tac)
      else
        let
          val outer_set_bds = set_bd_of_mrbnf outer;
          val inner_set_bdss = map set_bd_of_mrbnf inners;
         (* val inner_bd_Card_orders = map bd_Card_order_of_mrbnf inners;
          val _ = var_regular_of_mrbnf outer
          fun single_set_bd_thm i j =  @{thm comp_single_regular_set_bd}
            OF [bd_Cinfinite_of_mrbnf (nth inners j), bd_card_order_of_mrbnf (nth inners j),@{thm _}(* var_regular_of_mrbnf (nth inners j)*),
              bd_Cinfinite_of_mrbnf outer, bd_card_order_of_mrbnf outer, @{thm _}(*var_regular_of_mrbnf outer*), nth (nth inner_set_bdss j) i,
              nth outer_set_bds j]
           val _ = bd_Cinfinite_of_mrbnf outer
          val _ = var_regular_of_mrbnf outer *)
          fun single_set_bd_thm i j =  @{thm comp_single_regular_set_bd}
            OF [bd_infinite_regular_card_order_of_mrbnf (nth inners j),
              bd_infinite_regular_card_order_of_mrbnf outer, nth (nth inner_set_bdss j) i,
              nth outer_set_bds j]
           val single_set_bd_thmss = let val ssbdthm = map single_set_bd_thm (0 upto num_ilives - 1)
            in map (fn f => map f (0 upto (live_of_mrbnf outer) - 1)) ssbdthm end
            (*map ((fn f => map f (0 upto olive - 1)) o single_set_bd_thm) (0 upto ilive - 1);*)
        in
          @{map 3} (fn set'_eq_set => fn set_alt => fn single_set_bds => fn ctxt =>
            mk_comp_set_bd_tac ctxt set'_eq_set bd_ordIso_natLeq_thm_opt set_alt single_set_bds)
          (cond_keep set'_eq_sets is_ilive) (cond_keep set_alt_thms is_ilive)
          single_set_bd_thmss
        end;

    (*copied from BNF_Comp_Tactics*)
    val comp_in_alt_thms = @{thms o_apply collect_def image_insert image_empty Union_insert UN_insert
      UN_empty Union_empty Un_empty_right Union_Un_distrib Un_subset_iff conj_subset_def UN_image_subset
      conj_assoc};

    (*copied from BNF_Comp_Tactics*)
    fun mk_comp_in_alt_tac' ctxt comp_set_alts =
      unfold_thms_tac ctxt comp_set_alts THEN
      unfold_thms_tac ctxt comp_in_alt_thms THEN
      unfold_thms_tac ctxt @{thms set_eq_subset} THEN
      rtac ctxt conjI 1 THEN
      REPEAT_DETERM (
        rtac ctxt @{thm subsetI} 1 THEN
        unfold_thms_tac ctxt @{thms mem_Collect_eq Ball_def} THEN
        (REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
         REPEAT_DETERM (CHANGED ((
           (rtac ctxt conjI THEN' (assume_tac ctxt ORELSE' rtac ctxt subset_UNIV)) ORELSE'
           assume_tac ctxt ORELSE'
           (rtac ctxt subset_UNIV)) 1)) ORELSE rtac ctxt subset_UNIV 1))
      THEN TRYALL (Skip_Proof.cheat_tac ctxt)

    val (in_alt_thm, in_alt_lthy) =
      let
        val (Asets, lthy') = mk_Frees "A" (map HOLogic.mk_setT As) names_lthy;
        val inx = mk_in Asets (cond_keep sets is_ilive) oT;
        val iterms = map2 (mk_in Asets) (map (fn xs => cond_keep xs is_ilive) inner_setss) iTs
        val in_alt = mk_in iterms (cond_keep outer_sets is_olive) oT;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        (Goal.prove_sorry lthy [] [] goal
          (fn {context = ctxt, prems = _} => mk_comp_in_alt_tac' ctxt set_alt_thms)
        |> Thm.close_derivation \<^here>,
        lthy')
      end;

    fun le_rel_OO_tac ctxt = mk_le_rel_OO_tac ctxt (le_rel_OO_of_mrbnf outer) (rel_mono_of_mrbnf outer)
      (map le_rel_OO_of_mrbnf inners)

    fun rel_OO_Grp_tac ctxt =
      let
        val outer_rel_Grp = rel_Grp_of_mrbnf outer RS sym;
        val thm =
          trans OF [in_alt_thm RS @{thm OO_Grp_cong},
             trans OF [@{thm arg_cong2[of _ _ _ _ relcompp]} OF
               [trans OF [outer_rel_Grp RS @{thm arg_cong[of _ _ conversep]},
                 rel_conversep_of_mrbnf outer RS sym], outer_rel_Grp],
               trans OF [rel_OO_of_mrbnf outer RS sym, rel_cong0_of_mrbnf outer OF
                 (map (fn mrbnf => rel_OO_Grp_of_mrbnf mrbnf RS sym) inners)]]] RS sym;
      in
        unfold_thms_tac ctxt set'_eq_sets THEN rtac ctxt thm 1
      end;

    fun pred_set_tac ctxt =
      let
        val pred_alt = unfold_thms ctxt @{thms Ball_Collect}
          (trans OF [pred_cong0_of_mrbnf outer OF map pred_set_of_mrbnf inners, pred_set_of_mrbnf outer]);
        val in_alt = in_alt_thm RS @{thm Collect_inj} RS sym;
      in
        unfold_thms_tac ctxt (@{thm Ball_Collect} :: set'_eq_sets) THEN
        HEADGOAL (rtac ctxt (trans OF [pred_alt, in_alt]))
      end;

    val (wits, wit_tac, wit_lthy) =
      let
        val num_owits = nwits_of_mrbnf outer;
        val (xs, lthy') = mk_Frees "x" As in_alt_lthy;

        val outer_wits = mk_wits_of_mrbnf (replicate num_owits oDs) (replicate num_owits iTs) (replicate num_owits Bs) (replicate num_owits Fs) outer;

        val inner_witss = map (map (fn (I, wit) => Term.list_comb (wit, map (nth xs) I)))
          (@{map 3} (fn Ds => fn n => mk_wits_of_mrbnf (replicate n Ds) (replicate n As) (replicate n Bs) (replicate n Fs))
            iDss (map nwits_of_mrbnf inners) inners);

        val inner_witsss = map (map (nth inner_witss) o fst) outer_wits;

        val wits = (inner_witsss, (map (single o snd) outer_wits))
          |-> map2 (fold (map_product (fn iwit => fn owit => owit $ iwit)))
          |> flat
          |> map (`(fn t => Term.add_frees t []))
          |> minimize_wits
          |> map (fn (frees, t) => fold absfree frees t);

        fun wit_tac ctxt =
          mk_comp_wit_tac ctxt set'_eq_sets (wit_thms_of_mrbnf outer) (collect_set_map_of_mrbnf outer)
            (maps wit_thms_of_mrbnf inners);
      in (wits, wit_tac, lthy') end;

    (* Define the map function of the composed MRBNF. It instantiates the map function of outer with the map functions of the inners:
     * \<forall>f1 ... fn v1 ... vm u1 ... ul. outer.map (inner_1.map f1 ... fn v1 ... vm u1 ... ul) ... (inner_m.map f1 ... fn v1 ... vm u1 ... ul) v1 ... vm u1 ... ul
     * Although in the example above the map function first takes all of the live variable functions, then all the bound variable function and
     * lastly the free variable functions, this does NOT have to be the case. Lives, bounds and frees can be interleaved in any order.
     * Additionally, the inners are only instanciated as the live variables of the outer, so the map function retains the functions for bounds and frees *)
    val (mapx, map_lthy) =
      let
        (* Create new variables for the different variable kinds and give them the types:
         *  - live: f1 ... fn : As\<^sub>i \<Rightarrow> As'\<^sub>i
         *  - bound: v1 ... vm : Bs\<^sub>j \<Rightarrow> Bs\<^sub>j
         *  - free: u1 ... ul : Fs\<^sub>k \<Rightarrow> Fs\<^sub>k *)
        val (((fs, vs), us), lthy) = wit_lthy
          |> apfst snd o BNF_Util.mk_Frees' "f" (map2 (curry op -->) As As')
          ||>> apfst snd o BNF_Util.mk_Frees' "v" (map2 (curry op -->) Bs Bs)
          ||>> apfst snd o BNF_Util.mk_Frees' "u" (map2 (curry op -->) Fs Fs)

        val fn_vars = interlace fs vs us ivar_types;

        (* Create a list of the de Bruijn indices of the forall-bound function variables, and one list with only the frees and bounds *)
        val fn_vars_ids = map Bound (num_inondead - 1 downto 0);
        val fn_bounds_frees_ids = map fst (filter (fn x => snd x <> Live_Var) (fn_vars_ids ~~ ivar_types))

        (* As the forall-bound function variables over live, bound and free variables are already in the correct order,
         * the inner maps can be applied directly to those function variables *)
        val innermaps = map2 (fn deads => fn inner => Term.list_comb (mk_map_of_mrbnf deads As As' Bs Fs inner, fn_vars_ids)) iDss inners

        (* The outer map function needs to be applied with the inner map functions for all its live variable functions,
         * and with the forall-bound bound and free variable function variables in the correct order.
         * For this, we need to interlace the inner map function with the function variables according to the variable types of the outer *)
        fun interlace_maps _ _ [] = []
          | interlace_maps ids (f::maps) (Live_Var::ts) = f :: interlace_maps ids maps ts
          | interlace_maps (i::ids) maps (_::ts) = i :: interlace_maps ids maps ts
        val body = Term.list_comb (mk_map_of_mrbnf oDs iTs iTs' Bs Fs outer, interlace_maps fn_bounds_frees_ids innermaps (var_types_of_mrbnf outer))

      in (fold_rev Term.abs fn_vars body, lthy) end;

    (* The relator for the composed MRBNF just instantiates the variables of the outer relator with the relators of the inners
     * \<forall>Q1 ... Qn. outer.rel (inner1.rel Q1 ... Qn) ... (innerm.rel Q1 ... Qn)
     * The same happens for the predicator *)
    val (rel, pred, rel_lthy) =
      let
        (* Invent new variable names for relator and predicator prop variables *)
        val ((Qs, Ps), lthy') = map_lthy
          |> apfst snd o BNF_Util.mk_Frees' "Q" (map2 BNF_Util.mk_pred2T As As')
          ||>> apfst snd o BNF_Util.mk_Frees' "P" (map BNF_Util.mk_pred1T As);
        (* Contrary to "map" the relator/predicator only works over the live variables, so no interlacing needed here *)
        fun mk_innerf f Ds inner = Term.list_comb (f Ds As As' Bs Fs inner, map Bound (num_ilives - 1 downto 0));
        fun mk_f f vars = fold_rev Term.abs vars (Term.list_comb (f oDs iTs iTs' Bs Fs outer, map2 (mk_innerf f) iDss inners))
      in (mk_f mk_rel_of_mrbnf Qs, mk_f (fn Ds => fn Ts => K (mk_pred_of_mrbnf Ds Ts)) Ps, lthy') end;

    val tacs = {
      map_id0 = map_id0_tac,
      map_comp0 = map_comp0_tac,
      map_cong0 = map_cong0_tac,
      set_map0 = replicate num_inondead (K all_tac) (*set_map0_tacs*),
      infinite_regular_card_order = K all_tac (*bd_infinite_regular_card_order_tac*),
      set_bd = replicate num_inondead (K all_tac) (*set_bd_tacs*),
      le_rel_OO = K all_tac (*le_rel_OO_tac*),
      in_rel = K all_tac (*rel_OO_Grp_tac*),
      pred_set = K all_tac (*pred_set_tac*),
      wit = K all_tac (*wit_tac*)
    };

    val (mrbnf, lthy') = mrbnf_def Smart_Inline (K Dont_Note) true qualify tacs (SOME (oDs @ flat iDss)) (SOME (sort, cosort))
              Binding.empty Binding.empty Binding.empty [] (((((((binding, oT), mapx), ivar_types ~~ sets'), bd'), wits), SOME rel), SOME pred) rel_lthy

    val phi =
      Morphism.thm_morphism "MRBNF" (unfold_thms lthy' [id_mrbnf_def])
      $> Morphism.term_morphism "MRBNF" expand_id_mrbnf_def;

    val mrbnf' = morph_mrbnf phi mrbnf;
  in
    (mrbnf', (add_mrbnf_to_unfolds mrbnf' unfold_set, lthy'))
  end;

fun raw_multi_kill_mrbnf qualify targetTs mrbnf (accum as (unfold_set, lthy)) =
 (* if n = 0 then (mrbnf, accum) else*)
  let
    val n = 0
    val b = Binding.suffix_name (mk_killN n) (name_of_mrbnf mrbnf);
    val live = live_of_mrbnf mrbnf;
    val free = free_of_mrbnf mrbnf;
    val bound = bound_of_mrbnf mrbnf;
    val count = live + free + bound;
    val frees = frees_of_mrbnf mrbnf;
    val bounds = bounds_of_mrbnf mrbnf;
    val deads = deads_of_mrbnf mrbnf;
    val nwits = nwits_of_mrbnf mrbnf;
    val var_types = var_types_of_mrbnf mrbnf;
    val (class, coclass) = (class_of_mrbnf mrbnf, coclass_of_mrbnf mrbnf);

    (*Helper functions*)
    fun  cond_interlace _ _ [] = []
        | cond_interlace xs [] _ = xs
        | cond_interlace [] ys _ = ys
        | cond_interlace (x :: xs) ys (true :: bs) = x :: cond_interlace xs ys bs
        | cond_interlace xs (y :: ys) (false :: bs) = y :: cond_interlace xs ys bs

    (*Check if all conversions are legal*)
    (*Live > Free > Bound > Dead*)
    val _ = let
      exception Incompat_Var_Types
      fun var_leq Live_Var _ = true
        | var_leq Free_Var Live_Var = raise Incompat_Var_Types
        | var_leq Free_Var _ = true
        | var_leq Bound_Var Bound_Var = true
        | var_leq Bound_Var Dead_Var  = true
        | var_leq _ _ = raise Incompat_Var_Types
    in
      map2 var_leq var_types targetTs
    end
    (*calculate new variable counts*)
    val (new_live, new_free, new_bound) = let fun cocc v = filter (equal v) targetTs |> length
    in (cocc Live_Var,cocc Free_Var, cocc Bound_Var) end
    val (Atargets, Ftargets, Btargets) = let
      fun fil_var var_type = cond_keep targetTs (map (fn x => x = var_type) var_types)
    in (fil_var Live_Var, fil_var Free_Var, fil_var Bound_Var) end
    val new_count = new_live + new_free + new_bound
    val n = live - new_live;
    val isdemot_A = map (not_equal Live_Var) Atargets

    (* TODO: check 0 < n <= live *)
    (*`f = (f x, x)*)
    val (Ds, lthy1) = apfst (map TFree)
      (Variable.invent_types (map Type.sort_of_atyp deads) lthy);

   (* val ((killedAs, As), lthy2) = apfst (`(take (live - new_live)) o map TFree)
      (Variable.invent_types (replicate live @{sort type}) lthy1);*)
    val ( As, lthy2) = apfst (map TFree)
        (Variable.invent_types (cond_interlace (replicate live @{sort type}) (replicate live class)
          (map (fn x => x= Live_Var orelse x= Dead_Var) Atargets) ) lthy1)
    val demotedAs = cond_keep As isdemot_A

    val (As', lthy3) = let
      val (sAs', tlthy) = apfst (map TFree)
        (Variable.invent_types (replicate new_live @{sort type}) lthy2);
    in (cond_interlace demotedAs sAs' isdemot_A, tlthy) end
    (*val (As', lthy3) = apfst (map TFree) (Variable.invent_types (replicate live @{sort type}) lthy2);*)

    val (Fs, lthy4) = apfst (map TFree)
      (Variable.invent_types (replicate free class) lthy3);
    val (Bs, _(*lthy5*)) = apfst (map TFree)
      (Variable.invent_types (replicate free class) lthy4);

    val T = mk_T_of_mrbnf Ds As Bs Fs mrbnf;

    val mrbnf_sets = mk_sets_of_mrbnf (replicate count Ds) (replicate count As)
      (replicate count Bs) (replicate count Fs) mrbnf; (*sets before pruning*)

    val not_dead = map (not_equal Dead_Var) targetTs;
    val not_live = map (not_equal Live_Var) targetTs;
    val is_live_old = map (equal Live_Var) var_types;
    val is_live = map not not_live;
    val is_newlive = map (equal Live_Var) (filter (not_equal Dead_Var) targetTs); (*length = # of surviving vars*)
    val sets = cond_keep mrbnf_sets not_dead;
    val var_type_sets = cond_keep (targetTs ~~ mrbnf_sets) not_dead;

    val ((Asets, lives), _(*names_lthy*)) =
      let val still_lives = cond_keep As (map not isdemot_A) in lthy
      |> mk_Frees "A" (map HOLogic.mk_setT still_lives)
      ||>> mk_Frees "x" (still_lives) end;


    val ABF_types = map (HOLogic.dest_setT o range_type o fastype_of) mrbnf_sets;
    val new_deads = Ds @ cond_keep ABF_types (map (equal Dead_Var) targetTs)
    val A'BF_types = map (HOLogic.dest_setT o range_type o fastype_of) (mk_sets_of_mrbnf
      (replicate count Ds) (replicate count As') (replicate count Bs) (replicate count Fs) mrbnf);
    val ABF_living_types = cond_keep ABF_types not_dead;
    val A'BF_living_types = cond_keep A'BF_types not_dead;
    val ABF_lives = cond_keep ABF_types (map (equal Live_Var) var_types);
    val A'BF_lives = cond_keep A'BF_types (map (equal Live_Var) var_types);

    val fs = map2 (curry op -->) ABF_living_types A'BF_living_types;
    val killed_ids = map HOLogic.id_const (cond_keep (ABF_types) (map not not_dead));
(* (*Get types of lives, bounds and frees via image of set functions (not permuted)*)
    (*Create term list of permuted sets*)
    val (ABFsets, _(*names_lthy*)) = lthy
      |> mk_Frees "A" (map HOLogic.mk_setT (permute ABF_types));
    val rel = fold_rev Term.absdummy (permute_live (map2 mk_pred2T As As'))
      (Term.list_comb (mk_rel_of_mrbnf Ds As As' Bs Fs mrbnf, unpermute_live (*shorter permutation*) (map Bound (live - 1 downto 0))))
      |> Syntax.check_term lthy (*temporary*);
*)
    (*mrbnf.map id ... id*)
    val mapx =  fold_rev Term.absdummy fs
      (Term.list_comb (mk_map_of_mrbnf Ds As As' Bs Fs  mrbnf, cond_interlace
        (map Bound (new_count - 1 downto 0)) killed_ids not_dead));

(*Term.list_comb (mk_map_of_mrbnf Ds As As' Bs Fs mrbnf, map HOLogic.id_const killedAs);*)

    (*mrbnf.rel (op =) ... (op =)*)
    val demotedAs = cond_keep ABF_lives isdemot_A;
    val rs =
      let fun filter_lives xs = cond_keep xs (map not isdemot_A)
      in map2 mk_pred2T (filter_lives As) (filter_lives As') end;
    val rel = fold_rev Term.absdummy rs  (Term.list_comb (mk_rel_of_mrbnf Ds As As' Bs Fs mrbnf, cond_interlace (map HOLogic.eq_const demotedAs)
        (map Bound (new_live - 1 downto 0)) isdemot_A));
   (* val rel = Term.list_comb (mk_rel_of_mrbnf Ds As As' Bs Fs  mrbnf, map HOLogic.eq_const killedAs) |> @{print} |> Syntax.check_term lthy;*)

    (*mrbnf.pred (%_. True) ... (%_ True)*)
    val ps =
      let fun filter_lives xs = cond_keep xs (map not isdemot_A)
      in map mk_pred1T  (filter_lives As)  end;
    (*val pred = Term.list_comb (mk_pred_of_mrbnf Ds As Bs Fs mrbnf,
      map (fn T => Term.absdummy T @{term True}) killedAs);*)
    val pred = fold_rev Term.absdummy ps  (Term.list_comb (mk_pred_of_mrbnf Ds As Bs Fs mrbnf,
      cond_interlace (map (fn T => Term.absdummy T @{term True}) demotedAs)
        (map Bound (new_live - 1 downto 0)) isdemot_A));
    val bd = mk_bd_of_mrbnf Ds Bs Fs mrbnf;
    fun print_that_tac label ctxt tac = print_tac ctxt (label ^ " begin") THEN tac THEN print_tac ctxt (label ^ " end")

    fun map_id0_tac ctxt = rtac ctxt (map_id0_of_mrbnf mrbnf) 1 (*|> print_that_tac "map_id0" ctxt*);
    fun map_comp0_tac ctxt = rtac ctxt trans 1  THEN
      rtac ctxt (map_comp0_of_mrbnf mrbnf) 2 THEN
      TRYALL (rtac ctxt @{thm supp_id_bound} ORELSE' rtac ctxt @{thm bij_id} ORELSE'
        assume_tac ctxt) THEN
      unfold_thms_tac ctxt @{thms id_comp} THEN
      rtac ctxt refl 1  (*|> print_that_tac "map_comp0" ctxt*);

    fun map_cong0_tac ctxt =
      rtac ctxt (map_cong0_of_mrbnf mrbnf) 1
      THEN TRYALL (assume_tac ctxt)
      THEN TRYALL (Goal.assume_rule_tac ctxt)
      THEN TRYALL (rtac ctxt refl)
      THEN TRYALL (assume_tac ctxt)
      THEN TRYALL (rtac ctxt @{thm Prelim.supp_id_bound})
      THEN TRYALL (rtac ctxt @{thm Fun.bij_id})
      (*|> print_that_tac "map_cong0" ctxt*);

    val set_map0_tacs = map (fn thm => fn ctxt => rtac ctxt thm 1
      THEN TRYALL (assume_tac ctxt) THEN TRYALL (rtac ctxt @{thm Prelim.supp_id_bound})
        THEN TRYALL (rtac ctxt @{thm Fun.bij_id}) (*|> print_that_tac "map_map0" ctxt*))
          (cond_keep (set_map0_of_mrbnf mrbnf) not_dead );

    fun bd_infinite_regular_card_order_tac ctxt = rtac ctxt (bd_infinite_regular_card_order_of_mrbnf mrbnf) 1  (*|> print_that_tac "bd_card_order" ctxt*);
    val set_bd_tacs = map (fn thm => fn ctxt => rtac ctxt thm 1 (*|> print_that_tac "set_bd" ctxt*))
      (cond_keep (set_bd_of_mrbnf mrbnf) not_dead);

    fun mr_kill_in_alt_tac ctxt =
      ((rtac ctxt @{thm Collect_cong} THEN' rtac ctxt iffI) 1 THEN
      REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
      REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE'
        rtac ctxt conjI THEN' rtac ctxt subset_UNIV) 1)) THEN
      (rtac ctxt subset_UNIV ORELSE' assume_tac ctxt) 1 THEN
      REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
      REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE' assume_tac ctxt) 1))) ORELSE
      ((rtac ctxt @{thm UNIV_eq_I} THEN' rtac ctxt CollectI) 1 THEN
        REPEAT_DETERM (TRY (rtac ctxt conjI 1) THEN rtac ctxt subset_UNIV 1)) |> print_that_tac "in_alt" ctxt;

    val in_alt_thm =
      let
        val inx = mk_in Asets (cond_keep mrbnf_sets is_live) T; (*previously: mk_in Asets sets T*)
        val in_alt = mk_in (cond_interlace (map HOLogic.mk_UNIV demotedAs) Asets isdemot_A)
          (cond_keep  mrbnf_sets (map (equal Live_Var) var_types)) T;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
          mr_kill_in_alt_tac ctxt) |> Thm.close_derivation \<^here>
      end;

    fun le_rel_OO_tac ctxt =
      EVERY' [rtac ctxt @{thm ord_le_eq_trans}, rtac ctxt (le_rel_OO_of_mrbnf mrbnf)] 1 THEN
      unfold_thms_tac ctxt @{thms eq_OO} THEN rtac ctxt refl 1  (*|> print_that_tac "le_rel_OO" ctxt*);

    fun rel_OO_Grp_tac ctxt =
    let val mr_rel_Grp = mr_rel_Grp_of_mrbnf mrbnf;
        val mr_rel_cong0 = mr_rel_cong0_of_mrbnf mrbnf;
        val rel_cong0 = rel_cong0_of_mrbnf mrbnf;
        val supp_bij_ass_tac = rtac ctxt @{thm supp_id_bound} ORELSE' rtac ctxt @{thm bij_id}
         ORELSE' assume_tac ctxt
        val fun_cong_tac = (Subgoal.FOCUS_PARAMS (fn focus => let
        val ctxt = #context focus
        val t = #concl focus |> Thm.term_of
        val ((f, x), y) = Logic.strip_imp_concl t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd
          |> dest_comb |>> dest_comb
        val cf = Thm.cterm_of ctxt f
        val cx = Thm.cterm_of ctxt x
        val cy = Thm.cterm_of ctxt y
        val thm = infer_instantiate' ctxt [SOME cf, NONE, SOME cx, SOME cy] @{thm fun_cong[OF fun_cong]}
        in rtac ctxt (trans RS sym) 1 THEN rtac ctxt thm 1 end) ctxt 1)
    in
      fun_cong_tac
      THEN rtac ctxt ((in_alt_thm RS @{thm OO_Grp_cong}) RS trans) 1
      THEN rtac ctxt @{thm arg_cong2[of _ _ _ _ "(OO)"]} 1
      THEN rtac ctxt (@{thm arg_cong[of _ _ "conversep"]} RS trans) 1
      THEN (rtac ctxt (mr_rel_Grp RS sym) THEN_ALL_NEW supp_bij_ass_tac) 1
      THEN (rtac ctxt (mr_rel_conversep_of_mrbnf mrbnf RS sym) THEN_ALL_NEW supp_bij_ass_tac) 1
      THEN (rtac ctxt (mr_rel_Grp RS sym) THEN_ALL_NEW supp_bij_ass_tac) 1
      THEN unfold_thms_tac ctxt @{thms inv_id eq_alt[symmetric] conversep_eq}
      THEN (Subgoal.FOCUS_PARAMS (fn focus => let
        val ctxt = #context focus
        val t = #concl focus |> Thm.term_of
        val ((f, x), y) = Logic.strip_imp_concl t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst
          |> dest_comb |>> dest_comb
        val cf = Thm.cterm_of ctxt f
        val cx = Thm.cterm_of ctxt x
        val cy = Thm.cterm_of ctxt y
        val thm = infer_instantiate' ctxt [SOME cf, NONE, SOME cx, SOME cy] @{thm fun_cong[OF fun_cong]}
        val thm' = thm RS trans
        in rtac ctxt trans 1 THEN rtac ctxt thm 1 end) ctxt 1)
      THEN (rtac ctxt (mr_rel_OO_of_mrbnf mrbnf RS sym) THEN_ALL_NEW supp_bij_ass_tac) 1
      THEN unfold_thms_tac ctxt @{thms id_o o_id Grp_fst_snd eq_OO}
      THEN rtac ctxt trans 1
      THEN rtac ctxt (mr_rel_def_of_mrbnf mrbnf RS meta_eq_to_obj_eq |> BNF_Util.mk_unabs_def (count + new_live)) 1
      THEN (Subgoal.FOCUS_PARAMS (fn focus => let
        val ctxt = #context focus
        val t = #concl focus |> Thm.term_of |> Logic.strip_imp_concl |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd
        val (tr $ (tm $ _) $ _) = t
        val Rs = cond_keep (strip_comb tr |> snd) is_live_old
        val Fs = cond_keep (strip_comb tm |> snd) is_live_old
        val thm = infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) (Rs @ Fs))
            (hd (rel_map_of_mrbnf mrbnf))
          |> (fn thm => (thm RS box_equals RS sym) |> Drule.rotate_prems 1)
        in rtac ctxt thm 1 end) ctxt 1)
      THEN (rtac ctxt (rel_cong0 RS fun_cong RS fun_cong) THEN_ALL_NEW
        (SELECT_GOAL (unfold_thms_tac ctxt @{thms id_apply Grp_UNIV_def}) THEN_ALL_NEW rtac ctxt refl)) 1
      THEN rtac ctxt (rel_cong0 RS @{thm cong} RS fun_cong OF (replicate 5 refl)) 1
      THEN rtac ctxt (map_comp_of_mrbnf mrbnf RS trans) 1 THEN TRYALL supp_bij_ass_tac
      THEN unfold_thms_tac ctxt @{thms id_o o_id}
      THEN rtac ctxt refl 1 (*|> print_that_tac "rel_OO_Grp" ctxt*) end;

    fun pred_set_tac ctxt = mk_simple_pred_set_tac ctxt (pred_set_of_mrbnf mrbnf) in_alt_thm (*|> print_that_tac "pred_set" ctxt*);

    val mrbnf_wits = mk_wits_of_mrbnf (replicate nwits Ds) (replicate nwits As)
      (replicate nwits Bs) (replicate nwits Fs) mrbnf;

    val xs = cond_interlace (map (fn T => Const (@{const_name undefined}, T)) demotedAs) lives isdemot_A;
    val wits = map (fn t => fold absfree (Term.add_frees t []) t)
      (map (fn (I, wit) => Term.list_comb (wit, map (nth xs) I)) mrbnf_wits);

    fun wit_tac ctxt = mk_simple_wit_tac ctxt (wit_thms_of_mrbnf mrbnf) (*|> print_that_tac "wit" ctxt*);

    val tacs = {
      map_id0 = map_id0_tac,
      map_comp0 = map_comp0_tac,
      map_cong0 = map_cong0_tac,
      set_map0 = set_map0_tacs,
      infinite_regular_card_order = bd_infinite_regular_card_order_tac,
      set_bd = set_bd_tacs,
      le_rel_OO = le_rel_OO_tac,
      in_rel = rel_OO_Grp_tac,
      pred_set = pred_set_tac,
      wit = wit_tac
    };

    val (mrbnf', lthy') =
      mrbnf_def Smart_Inline (K Dont_Note) true qualify tacs (SOME new_deads) (SOME (class, coclass))
        Binding.empty Binding.empty Binding.empty []
        (((((((b, T), mapx), var_type_sets), bd), wits), SOME rel), SOME pred) lthy;
      val _ = @{print} "progress";

  in
    (mrbnf', (add_mrbnf_to_unfolds mrbnf' unfold_set, lthy'))
  end;

fun multi_kill_mrbnf qualify targetTs mrbnf (accum as ((cache, unfold_set), lthy)) =
  let val key = key_of_kill 0 mrbnf in (*TODO: replace 0 with something meaningful*)
    (case Typtab.lookup cache key of
      SOME (mrbnf, _) => (mrbnf, accum)
    | NONE => cache_comp_simple key cache (raw_multi_kill_mrbnf qualify targetTs mrbnf (unfold_set, lthy)))
  end;


(* Adding dummy variables n1-Frees, n2-Bounds, n3-Lives *)

fun raw_multilift_mrbnf qualify n1 n2 n3 mrbnf (accum as (unfold_set, lthy)) =
  if n1 + n2 + n3 = 0 then (mrbnf, accum) else
  let
    (*Read out various attributes of the mrbnf via accessor methods*)
    val b = Binding.suffix_name (mk_liftN (n1 + n2 + n3)) (name_of_mrbnf mrbnf);
    val live = live_of_mrbnf mrbnf;
    val deads = deads_of_mrbnf mrbnf;
    val free = free_of_mrbnf mrbnf;
    val frees = frees_of_mrbnf mrbnf;
    val bound = bound_of_mrbnf mrbnf;
    val bounds = bounds_of_mrbnf mrbnf;
    val nwits = nwits_of_mrbnf mrbnf;
    val class  = class_of_mrbnf mrbnf;
    val coclass = coclass_of_mrbnf mrbnf;
    val count = live + bound + free;
    val newcount = n1 + n2 + n3

    (* TODO: check 0 < n, m < 0, l < 0 *)

    val (Ds, lthy1) = apfst (map TFree)
      (Variable.invent_types (map Type.sort_of_atyp deads) lthy);
    val ((newAs, As), lthy2) = apfst (chop n3 o map TFree)
      (Variable.invent_types (replicate (n3 + live) @{sort type}) lthy1);
    val ((newAs', As'), lthy3) = apfst (chop n3 o map TFree)
      (Variable.invent_types (replicate (n3 + live) @{sort type}) lthy2);
    val ((newFs, Fs), lthy4) = apfst (chop n1 o map TFree)
      (Variable.invent_types (replicate n1 class @ map Type.sort_of_atyp frees) lthy3);
    val ((newBs, Bs), _(*lthy5*)) = apfst (chop n2 o map TFree)
      (Variable.invent_types (replicate n2 class @ map Type.sort_of_atyp bounds) lthy4);

    val newVars = newFs @ newBs @ newAs
    val newVars' = newFs @ newBs @ newAs'

    val T = mk_T_of_mrbnf Ds As Bs Fs mrbnf;

    val mrbnf_sets = mk_sets_of_mrbnf (replicate count Ds) (replicate count As)
      (replicate count Bs) (replicate count Fs) mrbnf;
    val sets = map (fn A => absdummy T (HOLogic.mk_set A [])) newVars @ mrbnf_sets;
    val var_type_sets = (replicate n1 Free_Var @ replicate n2 Bound_Var @  replicate n3 Live_Var
      @ var_types_of_mrbnf mrbnf) ~~ sets;

    val (Asets, _(*names_lthy*)) = lthy
      |> mk_Frees "A" (map (range_type o fastype_of) sets);


    (*%f1 ... fn. mrbnf.map*)
    val mapx =
      fold_rev Term.absdummy (map2 (curry op -->) newVars newVars')
        (mk_map_of_mrbnf Ds As As' Bs Fs mrbnf);

    (*%Q1 ... Qn. mrbnf.rel*)
    val rel = fold_rev Term.absdummy (map2 mk_pred2T newAs newAs')
      (mk_rel_of_mrbnf Ds As As' Bs Fs mrbnf);

    (*%P1 ... Pn. mrbnf.pred*)
    val pred = fold_rev Term.absdummy (map mk_pred1T newAs) (mk_pred_of_mrbnf Ds As Bs Fs mrbnf);

    val is_live = map (equal Live_Var o fst) var_type_sets
    fun print_that_tac label ctxt tac = print_tac ctxt (label ^ " begin") THEN tac THEN print_tac ctxt (label ^ " end")
    val bd = mk_bd_of_mrbnf Ds Bs Fs mrbnf;
    fun map_id0_tac ctxt = rtac ctxt (map_id0_of_mrbnf mrbnf) 1;
    fun map_comp0_tac ctxt = unfold_thms_tac ctxt (((map_comp0_of_mrbnf mrbnf RS sym)) ::
        @{thms comp_assoc id_comp comp_id}) THEN rtac ctxt refl 1 ;
    fun map_cong0_tac ctxt =
      rtac ctxt (map_cong0_of_mrbnf mrbnf) 1
      THEN REPEAT_DETERM_N (2 * (n1 + free + 2 * (n2 + bound))) (assume_tac ctxt 1)
      THEN REPEAT_DETERM_N (newcount + count) (Goal.assume_rule_tac ctxt 1);
    val set_map0_tacs =
      if Config.get lthy quick_and_dirty then
        ("quick n dirty", replicate (newcount + count) (K all_tac)) |> @{print warning} |> snd
      else
        replicate newcount (fn ctxt => empty_natural_tac ctxt) @
        map (fn thm => fn ctxt => HEADGOAL (rtac ctxt thm THEN_ALL_NEW assume_tac ctxt)) (set_map0_of_mrbnf mrbnf);

    fun bd_infinite_regular_card_order_tac ctxt = rtac ctxt (bd_infinite_regular_card_order_of_mrbnf mrbnf) 1;
    val set_bd_tacs =
      if Config.get lthy quick_and_dirty then
        replicate (newcount + count) (K all_tac)
      else
        replicate newcount (fn ctxt => HEADGOAL (rtac ctxt @{thm Cinfinite_gt_empty} THEN'
          rtac ctxt (bd_Cinfinite_of_mrbnf mrbnf))) @
        (map (fn thm => fn ctxt => rtac ctxt thm 1) (set_bd_of_mrbnf mrbnf));
    val in_alt_thm =
      let
        fun flt_lives xs = cond_keep xs is_live;
        val live_sets = flt_lives Asets (*previously, Asets was used instead of live_sets*)
        val inx = mk_in live_sets (flt_lives sets) T;
        val in_alt = mk_in (drop n3 live_sets) (cond_keep mrbnf_sets (drop newcount is_live)) T;
        val goal = fold_rev Logic.all live_sets (mk_Trueprop_eq (inx, in_alt));
      in
        Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} => lift_in_alt_tac ctxt)
        |> Thm.close_derivation \<^here>
      end;
    fun le_rel_OO_tac ctxt = rtac ctxt (le_rel_OO_of_mrbnf mrbnf) 1;

    fun mr_mk_simple_rel_OO_Grp_tac ctxt rel_OO_Grp in_alt_thm =
      HEADGOAL (rtac ctxt (trans OF [rel_OO_Grp, in_alt_thm RS @{thm OO_Grp_cong} RS sym]));


    fun mr_mk_simple_rel_OO_Grp_tac' ctxt rel_OO_Grp in_alt_thm = (rtac ctxt rel_OO_Grp 1)

    fun rel_OO_Grp_tac ctxt = unfold_thms_tac ctxt [in_alt_thm]
      THEN rtac ctxt (rel_OO_Grp_of_mrbnf mrbnf) 1
        THEN TRYALL (assume_tac ctxt) (*|> print_that_tac "rel_OO_grp" ctxt*);

    fun pred_set_tac ctxt = mk_simple_pred_set_tac ctxt (pred_set_of_mrbnf mrbnf) in_alt_thm (*|> print_that_tac "pred_set" ctxt*);

    val wits = map snd (mk_wits_of_mrbnf (replicate nwits Ds) (replicate nwits As)
      (replicate nwits Bs) (replicate nwits Fs) mrbnf);

    fun wit_tac ctxt = mk_simple_wit_tac ctxt (wit_thms_of_mrbnf mrbnf) (*|> print_that_tac "wit" ctxt*);

    val tacs = {
      map_id0 = map_id0_tac,
      map_comp0 = map_comp0_tac,
      map_cong0 = map_cong0_tac,
      set_map0 = set_map0_tacs,
      infinite_regular_card_order = bd_infinite_regular_card_order_tac,
      set_bd = set_bd_tacs,
      le_rel_OO = le_rel_OO_tac,
      in_rel = rel_OO_Grp_tac,
      pred_set = pred_set_tac,
      wit = wit_tac
    };

    val (mrbnf', lthy') =
      mrbnf_def Smart_Inline (K Dont_Note) true qualify tacs (SOME Ds) (SOME (class, coclass))
        Binding.empty Binding.empty Binding.empty []
        (((((((b, T), mapx), var_type_sets), bd), wits), SOME rel), SOME pred) lthy;

  in
    (mrbnf', (add_mrbnf_to_unfolds mrbnf' unfold_set, lthy'))
  end;

fun multilift_mrbnf qualify n m l mrbnf (accum as ((cache, unfold_set), lthy)) =
  let val key = key_of_multilift n m l mrbnf in
    (case Typtab.lookup cache key of
      SOME (mrbnf, _) => (mrbnf, accum)
    | NONE => cache_comp_simple key cache (raw_multilift_mrbnf qualify n m l mrbnf (unfold_set, lthy)))
  end;

(* Changing the order of live, free and bound variables *)
fun raw_permute_mrbnf qualify src dest mrbnf (accum as (unfold_set, lthy)) =
  if src = dest then (mrbnf, accum) else
  let
    (*Update binding's name to indicate permutation happened?*)
    val b = Binding.suffix_name (mk_permuteN src dest) (name_of_mrbnf mrbnf);
    (*Read out various attributes via accessor functions*)
    val live = live_of_mrbnf mrbnf;
    val free = free_of_mrbnf mrbnf;
    val bound = bound_of_mrbnf mrbnf;
    val count = live + free + bound;
    val deads = deads_of_mrbnf mrbnf;
    val bounds = bounds_of_mrbnf mrbnf;
    val frees = frees_of_mrbnf mrbnf;
    val var_types = var_types_of_mrbnf mrbnf;
    val nwits = nwits_of_mrbnf mrbnf;
    val (class, coclass) = (class_of_mrbnf mrbnf, coclass_of_mrbnf mrbnf)

    (*create permutation shorthands*)
    fun permute xs = permute_like_unique (op =) src dest xs;
    fun unpermute xs = permute_like_unique (op =) dest src xs;

    (*create shorthands for permutations of only live variables*)
    val is_live = map (equal Live_Var) var_types;
    val src_live = cond_keep src is_live;
    val dest_live = filter (fn x => exists (fn y => y = x ) src_live) dest;
    val is_live_perm = permute is_live;

    fun permute_live xs = permute_like_unique (op =) src_live dest_live xs;
    fun unpermute_live xs = permute_like_unique (op =) dest_live src_live xs;

    val (Ds, lthy1) = apfst (map TFree)
      (Variable.invent_types (map Type.sort_of_atyp deads) lthy);
    val (As, lthy2) = apfst (map TFree)
      (Variable.invent_types (replicate live @{sort type}) lthy1);
    val (As', lthy3) = apfst (map TFree)
      (Variable.invent_types (replicate live @{sort type}) lthy2);
    val (Fs, lthy4) = apfst (map TFree)
      (Variable.invent_types (map Type.sort_of_atyp frees) lthy3);
    val (Bs, _(*lthy5*)) = apfst (map TFree)
      (Variable.invent_types (map Type.sort_of_atyp bounds) lthy4);

    val T = mk_T_of_mrbnf Ds As Bs Fs mrbnf;

    val count = live + bound + free;

    (*Construct mrbnf's set functions*)
    val mrbnf_sets = mk_sets_of_mrbnf (replicate count Ds) (replicate count As)
      (replicate count Bs) (replicate count Fs) mrbnf;

    val sets = permute mrbnf_sets;
    val var_type_sets = permute (var_types_of_mrbnf mrbnf) ~~ sets;

    (*Get types of lives, bounds and frees via image of set functions (not permuted)*)
    val ABF_types = map (HOLogic.dest_setT o range_type o fastype_of) mrbnf_sets;
    val A'BF_types = map  (HOLogic.dest_setT o range_type o fastype_of) (mk_sets_of_mrbnf
      (replicate count Ds) (replicate count As') (replicate count Bs) (replicate count Fs) mrbnf);

    (*Create term list of permuted sets*)
    val (ABFsets, _(*names_lthy*)) = lthy
      |> mk_Frees "A" (map HOLogic.mk_setT (permute ABF_types));


    (*Create map functions permutation as lambda term*)
    (*%f(1) ... f(n). mrbnf.map f\<sigma>(1) ... f\<sigma>(n)*)
    val mapx = fold_rev Term.absdummy (permute (map2 (curry op -->) ABF_types A'BF_types))
      (Term.list_comb (mk_map_of_mrbnf Ds As As' Bs Fs  mrbnf, unpermute (map Bound (count - 1 downto 0))));

    (*Create relator permutation as lambda term*)
    (*%Q(1) ... Q(n). mrbnf.rel Q\<sigma>(1) ... Q\<sigma>(n)*)
    val rel = fold_rev Term.absdummy (permute_live (map2 mk_pred2T As As'))
      (Term.list_comb (mk_rel_of_mrbnf Ds As As' Bs Fs mrbnf, unpermute_live (*shorter permutation*) (map Bound (live - 1 downto 0))));


    (*%P(1) ... P(n). mrbnf.pred P\<sigma>(1) ... P\<sigma>(n)*)
    val pred = fold_rev Term.absdummy (permute_live (map mk_pred1T As)) (*As or ABFs?, short or long permuation*)
      (Term.list_comb (mk_pred_of_mrbnf Ds As Bs Fs mrbnf, unpermute_live (map Bound (live - 1 downto 0))))
      |> Syntax.check_term lthy (*temporary*);
      (*use shorter permutation*)

    val bd = mk_bd_of_mrbnf Ds Bs Fs mrbnf;
    fun prnttc label ctxt tac = print_tac ctxt (label ^ " begin") THEN tac THEN print_tac ctxt (label ^ " end")

    (*Proof obligations*)
    fun map_id0_tac ctxt = rtac ctxt (map_id0_of_mrbnf mrbnf) 1;
    fun map_comp0_tac ctxt = rtac ctxt (map_comp0_of_mrbnf mrbnf) 1
      THEN REPEAT_DETERM_N (live + 2*(free + bound)) (assume_tac ctxt 1);
    fun map_cong0_tac ctxt = rtac ctxt (map_cong0_of_mrbnf mrbnf) 1
      THEN REPEAT_DETERM_N (live  + 2*(free + bound)) (assume_tac ctxt 1)
      THEN REPEAT_DETERM_N count (Goal.assume_rule_tac ctxt 1);
    val set_map0_tacs = permute (map (fn thm => fn ctxt => rtac ctxt thm 1
      THEN REPEAT_DETERM_N count (assume_tac ctxt 1)) (set_map0_of_mrbnf mrbnf));
    fun bd_infinite_regular_card_order_tac ctxt = rtac ctxt (bd_infinite_regular_card_order_of_mrbnf mrbnf) 1;
    val set_bd_tacs = permute (map (fn thm => fn ctxt => rtac ctxt thm 1) (set_bd_of_mrbnf mrbnf));

    val in_alt_thm =
      let
        val Asets = cond_keep ABFsets is_live_perm (*ABFsets are already permuted*)
        val inx = mk_in Asets (cond_keep sets is_live_perm) T;
        val in_alt = mk_in (unpermute_live Asets) (cond_keep mrbnf_sets is_live) T;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
          mk_permute_in_alt_tac ctxt src_live dest_live)
        |> Thm.close_derivation \<^here>
      end;
    fun le_rel_OO_tac ctxt = rtac ctxt (le_rel_OO_of_mrbnf mrbnf) 1 |> prnttc "le_rel_OO" ctxt;

    fun rel_OO_Grp_tac ctxt = (unfold_thms_tac ctxt [in_alt_thm]) THEN (rtac ctxt (rel_OO_Grp_of_mrbnf mrbnf) 1)
      THEN TRYALL (assume_tac ctxt)
      |> prnttc "rel_OO_Grp" ctxt;
    fun pred_set_tac ctxt = mk_simple_pred_set_tac ctxt (pred_set_of_mrbnf mrbnf) in_alt_thm (*|> prnttc "pred_set" ctxt*);

    (*Nonemptiness witnesses*)
    val wits = map snd (mk_wits_of_mrbnf (replicate nwits Ds) (replicate nwits As)
        (replicate nwits Bs) (replicate nwits Fs) mrbnf);

    fun wit_tac ctxt = mk_simple_wit_tac ctxt (wit_thms_of_mrbnf mrbnf) (*|> prnttc "wit" ctxt*);

    val tacs = {
      map_id0 = map_id0_tac,
      map_comp0 = map_comp0_tac,
      map_cong0 = map_cong0_tac,
      set_map0 = set_map0_tacs,
      infinite_regular_card_order = bd_infinite_regular_card_order_tac,
      set_bd = set_bd_tacs,
      le_rel_OO = le_rel_OO_tac,
      in_rel = rel_OO_Grp_tac,
      pred_set = pred_set_tac,
      wit = wit_tac
    };

    val (mrbnf', lthy') =
      mrbnf_def Smart_Inline (K Dont_Note) true qualify tacs (SOME Ds) (SOME(class, coclass)) Binding.empty
        Binding.empty Binding.empty []
        (((((((b, T), mapx), var_type_sets), bd), wits), SOME rel), SOME pred) lthy;
  in
    (mrbnf', (add_mrbnf_to_unfolds mrbnf' unfold_set, lthy'))
  end;

fun permute_mrbnf qualify src dest mrbnf (accum as ((cache, unfold_set), lthy)) =
  let val key = key_of_permute src dest mrbnf in
    (case Typtab.lookup cache key of
      SOME (mrbnf, _) => (mrbnf, accum)
    | NONE => cache_comp_simple key cache (raw_permute_mrbnf qualify src dest mrbnf (unfold_set, lthy)))
  end;

(* Composition pipeline *)
(*
fun permute_and_kill_mrbnf qualify n src dest mrbnf =
  permute_mrbnf qualify src dest mrbnf
  #> uncurry (kill_mrbnf qualify n);
fun lift_and_permute_mrbnf qualify n src dest mrbnf =
  lift_mrbnf qualify n mrbnf
  #> uncurry (permute_mrbnf qualify src dest);
fun normalize_mrbnfs qualify Ass Ds flatten_tyargs mrbnfs accum =
  let
    val before_kill_src = map (fn As => 0 upto (length As - 1)) Ass;
    val kill_poss = map (find_indices op = Ds) Ass;
    val live_poss = map2 (subtract op =) kill_poss before_kill_src;
    val before_kill_dest = map2 append kill_poss live_poss;
    val kill_ns = map length kill_poss;
    val (inners', accum') =
      @{fold_map 5} (permute_and_kill_mrbnf o qualify)
        (if length mrbnfs = 1 then [0] else 1 upto length mrbnfs)
        kill_ns before_kill_src before_kill_dest mrbnfs accum;
    val Ass' = map2 (map o nth) Ass live_poss;
    val As = flatten_tyargs Ass';
    val after_lift_dest = replicate (length Ass') (0 upto (length As - 1));
    val old_poss = map (map (fn x => find_index (fn y => x = y) As)) Ass';
    val new_poss = map2 (subtract op =) old_poss after_lift_dest;
    val after_lift_src = map2 append new_poss old_poss;
    val lift_ns = map (fn xs => length As - length xs) Ass';
  in
    ((kill_poss, As), @{fold_map 5} (lift_and_permute_mrbnf o qualify)
      (if length mrbnfs = 1 then [0] else 1 upto length mrbnfs)
      lift_ns after_lift_src after_lift_dest inners' accum')
  end;
fun default_comp_sort Ass =
  Library.sort (Term_Ord.typ_ord o apply2 TFree) (fold (fold (insert (op =))) Ass []);
fun raw_compose_mrbnf const_policy qualify flatten_tyargs outer inners oDs Dss tfreess accum =
  let
    val b = name_of_mrbnf outer;
    val Ass = map (map Term.dest_TFree) tfreess;
    val Ds = fold (fold Term.add_tfreesT) (oDs :: Dss) [];
    val ((kill_poss, As), (inners', ((cache', unfold_set'), lthy'))) =
      normalize_mrbnfs qualify Ass Ds flatten_tyargs inners accum;
    val Ds =
      oDs @ flat (@{map 3} (uncurry append oo curry swap oo map o nth) tfreess kill_poss Dss);
    val As = map TFree As;
  in
    apfst (rpair (Ds, As))
      (apsnd (apfst (pair cache'))
        (clean_compose_mrbnf const_policy (qualify 0) b outer inners' (unfold_set', lthy')))
  end;
fun compose_mrbnf const_policy qualify flatten_tyargs outer inners oDs Dss tfreess
    (accum as ((cache, _), _)) =
  let val key = key_of_compose oDs Dss tfreess outer inners in
    (case Typtab.lookup cache key of
      SOME mrbnf_Ds_As => (mrbnf_Ds_As, accum)
    | NONE =>
      cache_comp key
        (raw_compose_mrbnf const_policy qualify flatten_tyargs outer inners oDs Dss tfreess accum))
  end;
(* Hide the type of the bound (optimization) and unfold the definitions (nicer to the user) *)
type absT_info =
  {absT: typ,
   repT: typ,
   abs: term,
   rep: term,
   abs_inject: thm,
   abs_inverse: thm,
   type_definition: thm};
fun morph_absT_info phi
  {absT, repT, abs, rep, abs_inject, abs_inverse, type_definition} =
  {absT = Morphism.typ phi absT,
   repT = Morphism.typ phi repT,
   abs = Morphism.term phi abs,
   rep = Morphism.term phi rep,
   abs_inject = Morphism.thm phi abs_inject,
   abs_inverse = Morphism.thm phi abs_inverse,
   type_definition = Morphism.thm phi type_definition};
fun mk_absT thy repT absT repU =
  let
    val rho = Vartab.fold (cons o apsnd snd) (Sign.typ_match thy (repT, repU) Vartab.empty) [];
  in Term.typ_subst_TVars rho absT end
  handle Type.TYPE_MATCH => raise Term.TYPE ("mk_absT", [repT, absT, repU], []);
fun mk_repT absT repT absU =
  if absT = repT then absU
  else
    (case (absT, absU) of
      (Type (C, Ts), Type (C', Us)) =>
        if C = C' then Term.typ_subst_atomic (Ts ~~ Us) repT
        else raise Term.TYPE ("mk_repT", [absT, repT, absU], [])
    | _ => raise Term.TYPE ("mk_repT", [absT, repT, absU], []));
fun mk_abs_or_rep _ absU (Const (@{const_name id_mrbnf}, _)) =
    Const (@{const_name id_mrbnf}, absU --> absU)
  | mk_abs_or_rep getT (Type (_, Us)) abs =
    let val Ts = snd (dest_Type (getT (fastype_of abs)))
    in Term.subst_atomic_types (Ts ~~ Us) abs end;
val mk_abs = mk_abs_or_rep range_type;
val mk_rep = mk_abs_or_rep domain_type;
fun maybe_typedef force_out_of_line (b, As, mx) set opt_morphs tac lthy =
  let
    val threshold = Config.get lthy typedef_threshold;
    val repT = HOLogic.dest_setT (fastype_of set);
    val out_of_line = force_out_of_line orelse
      (threshold >= 0 andalso Term.size_of_typ repT >= threshold);
  in
    if out_of_line then
      typedef (b, As, mx) set opt_morphs tac lthy
      |>> (fn (T_name, ({Rep_name, Abs_name, ...},
          {type_definition, Abs_inverse, Abs_inject, Abs_cases, ...}) : Typedef.info) =>
        (Type (T_name, map TFree As),
          (Rep_name, Abs_name, type_definition, Abs_inverse, Abs_inject, Abs_cases)))
    else
      ((repT,
        (@{const_name id_mrbnf}, @{const_name id_mrbnf},
         @{thm type_definition_id_mrbnf_UNIV},
         @{thm type_definition.Abs_inverse[OF type_definition_id_mrbnf_UNIV]},
         @{thm type_definition.Abs_inject[OF type_definition_id_mrbnf_UNIV]},
         @{thm type_definition.Abs_cases[OF type_definition_id_mrbnf_UNIV]})), lthy)
  end;
fun seal_mrbnf qualify (unfold_set : unfold_set) b force_out_of_line Ds all_Ds mrbnf lthy =
  let
    val live = live_of_mrbnf mrbnf;
    val nwits = nwits_of_mrbnf mrbnf;
    val ((As, As'), lthy1) = apfst (`(map TFree))
      (Variable.invent_types (replicate live @{sort type}) (fold Variable.declare_typ all_Ds lthy));
    val (Bs, _) = apfst (map TFree) (Variable.invent_types (replicate live @{sort type}) lthy1);
    val ((((fs, fs'), (Rs, Rs')), (Ps, Ps')), _(*names_lthy*)) = lthy
      |> mk_Frees' "f" (map2 (curry op -->) As Bs)
      ||>> mk_Frees' "R" (map2 mk_pred2T As Bs)
      ||>> mk_Frees' "P" (map mk_pred1T As);
    val repTA = mk_T_of_mrbnf Ds As mrbnf;
    val T_bind = qualify b;
    val repTA_tfrees = Term.add_tfreesT repTA [];
    val all_TA_params_in_order = fold_rev Term.add_tfreesT all_Ds As';
    val TA_params =
      (if force_out_of_line then all_TA_params_in_order
       else inter (op =) repTA_tfrees all_TA_params_in_order);
    val ((TA, (Rep_name, Abs_name, type_definition, Abs_inverse, Abs_inject, _)), lthy) =
      maybe_typedef force_out_of_line (T_bind, TA_params, NoSyn) (HOLogic.mk_UNIV repTA) NONE
        (fn ctxt => EVERY' [rtac ctxt exI, rtac ctxt UNIV_I] 1) lthy;
    val repTB = mk_T_of_mrbnf Ds Bs mrbnf;
    val TB = Term.typ_subst_atomic (As ~~ Bs) TA;
    val RepA = Const (Rep_name, TA --> repTA);
    val RepB = Const (Rep_name, TB --> repTB);
    val AbsA = Const (Abs_name, repTA --> TA);
    val AbsB = Const (Abs_name, repTB --> TB);
    val Abs_inject' = Abs_inject OF @{thms UNIV_I UNIV_I};
    val Abs_inverse' = Abs_inverse OF @{thms UNIV_I};
    val absT_info = {absT = TA, repT = repTA, abs = AbsA, rep = RepA, abs_inject = Abs_inject',
      abs_inverse = Abs_inverse', type_definition = type_definition};
    val mrbnf_map = fold_rev Term.absfree fs' (HOLogic.mk_comp (HOLogic.mk_comp (AbsB,
      Term.list_comb (mk_map_of_mrbnf Ds As Bs mrbnf, fs)), RepA));
    val mrbnf_sets = map ((fn t => HOLogic.mk_comp (t, RepA)))
      (mk_sets_of_mrbnf (replicate live Ds) (replicate live As) mrbnf);
    val mrbnf_bd = mk_bd_of_mrbnf Ds As mrbnf;
    val mrbnf_rel = fold_rev Term.absfree Rs' (mk_vimage2p RepA RepB $
      (Term.list_comb (mk_rel_of_mrbnf Ds As Bs mrbnf, Rs)));
    val mrbnf_pred = fold_rev Term.absfree Ps' (HOLogic.mk_comp
      (Term.list_comb (mk_pred_of_mrbnf Ds As mrbnf, Ps), RepA));
    (*bd may depend only on dead type variables*)
    val bd_repT = fst (dest_relT (fastype_of mrbnf_bd));
    val bdT_bind = qualify (Binding.suffix_name ("_" ^ bdTN) b);
    val params = Term.add_tfreesT bd_repT [];
    val all_deads = map TFree (fold_rev Term.add_tfreesT all_Ds []);
    val ((bdT, (_, Abs_bd_name, _, _, Abs_bdT_inject, Abs_bdT_cases)), lthy) =
      maybe_typedef false (bdT_bind, params, NoSyn) (HOLogic.mk_UNIV bd_repT) NONE
        (fn ctxt => EVERY' [rtac ctxt exI, rtac ctxt UNIV_I] 1) lthy;
    val (mrbnf_bd', bd_ordIso, bd_card_order, bd_cinfinite) =
      if bdT = bd_repT then (mrbnf_bd, bd_Card_order_of_mrbnf mrbnf RS @{thm ordIso_refl},
        bd_card_order_of_mrbnf mrbnf, bd_cinfinite_of_mrbnf mrbnf)
      else
        let
          val mrbnf_bd' = mk_dir_image mrbnf_bd (Const (Abs_bd_name, bd_repT --> bdT));
          val Abs_bdT_inj = mk_Abs_inj_thm Abs_bdT_inject;
          val Abs_bdT_bij = mk_Abs_bij_thm lthy Abs_bdT_inj Abs_bdT_cases;
          val bd_ordIso = @{thm dir_image} OF [Abs_bdT_inj, bd_Card_order_of_mrbnf mrbnf];
          val bd_card_order =
            @{thm card_order_dir_image} OF [Abs_bdT_bij, bd_card_order_of_mrbnf mrbnf];
          val bd_cinfinite =
            (@{thm Cinfinite_cong} OF [bd_ordIso, bd_Cinfinite_of_mrbnf mrbnf]) RS conjunct1;
        in
          (mrbnf_bd', bd_ordIso, bd_card_order, bd_cinfinite)
        end;
    fun map_id0_tac ctxt =
      rtac ctxt (@{thm type_copy_map_id0} OF [type_definition, map_id0_of_mrbnf mrbnf]) 1;
    fun map_comp0_tac ctxt =
      rtac ctxt (@{thm type_copy_map_comp0} OF [type_definition, map_comp0_of_mrbnf mrbnf]) 1;
    fun map_cong0_tac ctxt =
      EVERY' (rtac ctxt @{thm type_copy_map_cong0} :: rtac ctxt (map_cong0_of_mrbnf mrbnf) ::
        map (fn i => EVERY' [select_prem_tac ctxt live (dtac ctxt meta_spec) i, etac ctxt meta_mp,
          etac ctxt (o_apply RS equalityD2 RS set_mp)]) (1 upto live)) 1;
    fun set_map0_tac thm ctxt =
      rtac ctxt (@{thm type_copy_set_map0} OF [type_definition, thm]) 1;
    val set_bd_tacs = map (fn thm => fn ctxt => rtac ctxt (@{thm ordLeq_ordIso_trans} OF
        [thm, bd_ordIso] RS @{thm type_copy_set_bd}) 1) (set_bd_of_mrbnf mrbnf);
    fun le_rel_OO_tac ctxt =
      rtac ctxt (le_rel_OO_of_mrbnf mrbnf RS @{thm vimage2p_relcompp_mono}) 1;
    fun rel_OO_Grp_tac ctxt =
      (rtac ctxt (rel_OO_Grp_of_mrbnf mrbnf RS @{thm vimage2p_cong} RS trans) THEN'
       (if force_out_of_line then subst_tac ctxt NONE else SELECT_GOAL o unfold_thms_tac ctxt)
         [type_definition RS @{thm vimage2p_relcompp_converse}] THEN'
       SELECT_GOAL (unfold_thms_tac ctxt [o_apply,
         type_definition RS @{thm type_copy_vimage2p_Grp_Rep},
         type_definition RS @{thm vimage2p_relcompp_converse}]) THEN'
       rtac ctxt refl) 1;
    fun pred_set_tac ctxt =
      HEADGOAL (EVERY'
        [rtac ctxt (pred_set_of_mrbnf mrbnf RS @{thm arg_cong[of _ _ "\<lambda>f. f \<circ> _"]} RS trans),
        SELECT_GOAL (unfold_thms_tac ctxt (@{thms Ball_comp_iff conj_comp_iff})), rtac ctxt refl]);
    val tacs = zip_axioms map_id0_tac map_comp0_tac map_cong0_tac
      (map set_map0_tac (set_map0_of_mrbnf mrbnf))
      (fn ctxt => rtac ctxt bd_card_order 1) (fn ctxt => rtac ctxt bd_cinfinite 1)
      set_bd_tacs le_rel_OO_tac rel_OO_Grp_tac pred_set_tac;
    val mrbnf_wits = map (fn (I, t) =>
        fold Term.absdummy (map (nth As) I)
          (AbsA $ Term.list_comb (t, map Bound (0 upto length I - 1))))
      (mk_wits_of_mrbnf (replicate nwits Ds) (replicate nwits As) mrbnf);
    fun wit_tac ctxt =
      ALLGOALS (dtac ctxt (type_definition RS @{thm type_copy_wit})) THEN
      mk_simple_wit_tac ctxt (wit_thms_of_mrbnf mrbnf);
    val (mrbnf', lthy') =
      mrbnf_def Hardly_Inline (user_policy Dont_Note) true qualify tacs wit_tac (SOME all_deads)
        Binding.empty Binding.empty Binding.empty []
        (((((((b, TA), mrbnf_map), mrbnf_sets), mrbnf_bd'), mrbnf_wits), SOME mrbnf_rel), SOME mrbnf_pred) lthy;
    val unfolds = @{thm id_mrbnf_apply} ::
      (#map_unfolds unfold_set @ flat (#set_unfoldss unfold_set) @ #rel_unfolds unfold_set);
    val mrbnf'' = mrbnf' |> morph_mrbnf_defs (Morphism.thm_morphism "BNF" (unfold_thms lthy' unfolds));
    val map_def = map_def_of_mrbnf mrbnf'';
    val set_defs = set_defs_of_mrbnf mrbnf'';
    val rel_def = rel_def_of_mrbnf mrbnf'';
    val mrbnf_b = qualify b;
    val def_qualify =
      Thm.def_binding o Binding.concealed o Binding.qualify false (Binding.name_of mrbnf_b);
    fun mk_prefix_binding pre = Binding.prefix_name (pre ^ "_") mrbnf_b;
    val map_b = def_qualify (mk_prefix_binding mapN);
    val rel_b = def_qualify (mk_prefix_binding relN);
    val set_bs = if live = 1 then [def_qualify (mk_prefix_binding setN)]
      else map (def_qualify o mk_prefix_binding o mk_setN) (1 upto live);
    val notes = (map_b, map_def) :: (rel_b, rel_def) :: (set_bs ~~ set_defs)
      |> map (fn (b, def) => ((b, []), [([def], [])]))
    val (noted, lthy'') = lthy'
      |> Local_Theory.notes notes
      ||> (if repTA = TA then I else register_mrbnf_raw (fst (dest_Type TA)) mrbnf'')
  in
    ((morph_mrbnf (substitute_noted_thm noted) mrbnf'', (all_deads, absT_info)), lthy'')
  end;
exception BAD_DEAD of typ * typ;
fun mrbnf_of_typ _ _ _ _ _ Ds0 (T as TFree T') accum =
    (if member (op =) Ds0 T' then (DEADID_mrbnf, ([T], [])) else (ID_mrbnf, ([], [T])), accum)
  | mrbnf_of_typ _ _ _ _ _ _ (TVar _) _ = error "Unexpected schematic variable"
  | mrbnf_of_typ optim const_policy qualify' flatten_tyargs Xs Ds0 (T as Type (C, Ts))
      (accum as (_, lthy)) =
    let
      fun check_bad_dead ((_, (deads, _)), _) =
        let val Ds = fold Term.add_tfreesT deads [] in
          (case Library.inter (op =) Ds Xs of [] => ()
          | X :: _ => raise BAD_DEAD (TFree X, T))
        end;
      val tfrees = subtract (op =) Ds0 (Term.add_tfreesT T []);
      val mrbnf_opt = if null tfrees then NONE else mrbnf_of lthy C;
    in
      (case mrbnf_opt of
        NONE => ((DEADID_mrbnf, ([T], [])), accum)
      | SOME mrbnf =>
        if optim andalso forall (can Term.dest_TFree) Ts andalso length Ts = length tfrees then
          let
            val T' = T_of_mrbnf mrbnf;
            val deads = deads_of_mrbnf mrbnf;
            val lives = lives_of_mrbnf mrbnf;
            val tvars' = Term.add_tvarsT T' [];
            val Ds_As =
              apply2 (map (Term.typ_subst_TVars (map fst tvars' ~~ map TFree tfrees)))
                (deads, lives);
          in ((mrbnf, Ds_As), accum) end
        else
          let
            val name = Long_Name.base_name C;
            fun qualify i =
              let val namei = name ^ nonzero_string_of_int i;
              in qualify' o Binding.qualify true namei end;
            val odead = dead_of_mrbnf mrbnf;
            val olive = live_of_mrbnf mrbnf;
            val Ds = map (fn i => TFree (string_of_int i, [])) (1 upto odead);
            val Us = snd (Term.dest_Type (mk_T_of_mrbnf Ds (replicate olive dummyT) mrbnf));
            val oDs_pos = map (fn x => find_index (fn y => x = y) Us) Ds
              |> filter (fn x => x >= 0);
            val oDs = map (nth Ts) oDs_pos;
            val Ts' = map (nth Ts) (subtract (op =) oDs_pos (0 upto length Ts - 1));
            val ((inners, (Dss, Ass)), (accum', lthy')) =
              apfst (apsnd split_list o split_list) (@{fold_map 2}
                (fn i => mrbnf_of_typ optim Smart_Inline (qualify i) flatten_tyargs Xs Ds0)
                (if length Ts' = 1 then [0] else 1 upto length Ts') Ts' accum);
          in
            compose_mrbnf const_policy qualify flatten_tyargs mrbnf inners oDs Dss Ass (accum', lthy')
          end)
      |> tap check_bad_dead
    end;
*)
end;