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

  exception BAD_DEAD of typ * typ

  val mrbnf_of_typ: bool -> MRBNF_Def.inline_policy -> (binding -> binding) ->
    ((string * sort) list list -> (string * sort) list) -> (string * sort) list ->
    (string * sort) list -> ((string * sort) * MRBNF_Def.var_type) list -> typ -> (comp_cache * unfold_set) * local_theory ->
    (MRBNF_Def.mrbnf * (typ list * typ list)) * ((comp_cache * unfold_set) * local_theory)

  val clean_compose_mrbnf: MRBNF_Def.inline_policy -> (binding -> binding) -> binding -> MRBNF_Def.mrbnf ->
    MRBNF_Def.mrbnf list -> unfold_set * local_theory -> MRBNF_Def.mrbnf * (unfold_set * local_theory)
  val permute_mrbnf: (binding -> binding) -> int list -> int list -> MRBNF_Def.mrbnf ->
    (comp_cache * unfold_set) * local_theory -> MRBNF_Def.mrbnf * ((comp_cache * unfold_set) * local_theory)
  val normalize_mrbnfs: (int -> binding -> binding) -> (string * sort) option list ->
    (string * sort) list list -> (string * sort) list -> ((string * sort) * MRBNF_Def.var_type) list ->
    ((string * sort) list list ->
    (string * sort) list) -> MRBNF_Def.mrbnf option ->  MRBNF_Def.mrbnf list -> (comp_cache * unfold_set) * local_theory ->
    (int list list * (string * sort) list) * MRBNF_Def.mrbnf option * (MRBNF_Def.mrbnf list * ((comp_cache * unfold_set) * local_theory))
  val compose_mrbnf: MRBNF_Def.inline_policy -> (int -> binding -> binding) ->
    ((string * sort) list list -> (string * sort) list) -> MRBNF_Def.mrbnf -> MRBNF_Def.mrbnf list ->
    typ list -> typ list list -> typ option list -> typ list list ->
    ((string * sort) * MRBNF_Def.var_type) list -> (comp_cache * unfold_set) * local_theory ->
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
    MRBNF_Def.mrbnf -> local_theory -> (MRBNF_Def.mrbnf * (typ list * absT_info)) * local_theory
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
  key_of_typess "" [[T_of_mrbnf mrbnf], lives_of_mrbnf mrbnf, frees_of_mrbnf mrbnf, bounds_of_mrbnf mrbnf, sort Term_Ord.typ_ord (deads_of_mrbnf mrbnf)];
fun typ_of_var_type MRBNF_Def.Live_Var = Type ("Live_Var", [])
  | typ_of_var_type MRBNF_Def.Free_Var = Type ("Free_Var", [])
  | typ_of_var_type MRBNF_Def.Bound_Var = Type ("Bound_Var", [])
  | typ_of_var_type MRBNF_Def.Dead_Var = Type ("Dead_Var", [])

fun key_of_demote var_types mrbnf = key_of_types "d" (map typ_of_var_type var_types @ [typ_of_mrbnf mrbnf]);
fun key_of_lift (n1, n2, n3) mrbnf = key_of_types "l+" [typ_of_int n1, typ_of_int n2, typ_of_int n3, typ_of_mrbnf mrbnf];

fun key_of_permute src dest mrbnf =
  key_of_types "p" (map typ_of_int src @ map typ_of_int dest @ [typ_of_mrbnf mrbnf]);
fun key_of_compose oDs Dss oAs Ass outer inners =
  key_of_types "c" (map (key_of_typess "") [[oDs], Dss, [oAs], Ass, [map typ_of_mrbnf (outer :: inners)]]);

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
fun mk_liftN (n1, n2, n3) = "_lift" ^ string_of_int n1 ^ "_" ^ string_of_int n2 ^ "_" ^ string_of_int n3;
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
    val num_olives = live_of_mrbnf outer;
    val num_free = free_of_mrbnf outer;
    val num_bound = bound_of_mrbnf outer;
    val num_inondead = num_ilives + num_free + num_bound;
    val num_onondead = live_of_mrbnf outer + num_free + num_bound;
    val ivar_types = var_types_of_mrbnf (hd inners);
    val ovar_types = var_types_of_mrbnf outer;
    val is_ilive = map (equal Live_Var) ivar_types;
    val is_olive = map (equal Live_Var) ovar_types;

    val sort = fold (curry (Sign.inter_sort (Proof_Context.theory_of lthy))) (map class_of_mrbnf inners) (class_of_mrbnf outer);
    val cosort = fold (curry (Sign.inter_sort (Proof_Context.theory_of lthy))) (map coclass_of_mrbnf inners) (coclass_of_mrbnf outer);

    fun try_unprefix prfx s = case try (unprefix prfx) s of
      SOME x => x
      | NONE => s
    fun mk_class prfx xs lthy =
      let
        val name = prfx ^ space_implode "" (map (try_unprefix prfx o short_type_name) xs)
      in
        Local_Theory.background_theory_result (fn thy =>
          let val (class, lthy) = Class_Declaration.class (Binding.concealed (qualify (Binding.name name))) [] xs [] thy
          in ([class], Local_Theory.exit_global lthy) end
        ) lthy
      end;
    val ((class, coclass), lthy) = lthy
      |> mk_class "var_" sort
      ||>> mk_class "covar_" cosort;

    val ((((((oDs, iDss), As), As'), Fs), Bs), names_lthy) = lthy
      |> mk_TFrees' (map Type.sort_of_atyp (deads_of_mrbnf outer))
      ||>> fold_map mk_TFrees' (map (map Type.sort_of_atyp o deads_of_mrbnf) inners)
      ||>> mk_TFrees num_ilives
      ||>> mk_TFrees num_ilives
      ||>> mk_TFrees' (replicate (free_of_mrbnf outer) class)
      ||>> mk_TFrees' (replicate (bound_of_mrbnf outer) class);

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
      mr_mk_comp_bd_card_order_tac ctxt (map bd_infinite_regular_card_order_of_mrbnf inners) (SOME (bd_infinite_regular_card_order_of_mrbnf outer));

    val outer_sets = mk_sets_of_mrbnf (replicate num_onondead oDs) (replicate num_onondead iTs)
      (replicate num_onondead Bs) (replicate num_onondead Fs) outer;
    val inner_setss = map2 (fn Ds => mk_sets_of_mrbnf (replicate num_inondead Ds)
      (replicate num_inondead As) (replicate num_inondead Bs) (replicate num_inondead Fs))
      iDss inners;

    val (sets, sets_alt) =
      let
        val ivars = ivar_types ~~ interlace As Bs Fs ivar_types;
        fun mk_outer_sets' osets ovar_types [] = []
          | mk_outer_sets' (_::osets) (Live_Var::ovar_types) ivar_types = mk_outer_sets' osets ovar_types ivar_types
          | mk_outer_sets' osets ovar_types (Live_Var::ivar_types) = NONE::mk_outer_sets' osets ovar_types ivar_types
          | mk_outer_sets' (s::osets) (_::ovar_types) (_::ivar_types) = SOME s::mk_outer_sets' osets ovar_types ivar_types
        val outer_sets' = mk_outer_sets' outer_sets ovar_types ivar_types

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
              | _ => mk_union (the (nth outer_sets' i) $ Bound 0, u)
            );
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
      mr_mk_comp_set_map0_tac ctxt i (nth set'_eq_sets i) (map_comp0_of_mrbnf outer)
        (set_map0_of_mrbnf outer) (map ((fn thms => nth thms i) o set_map0_of_mrbnf) inners)
        ovar_types ivar_types

    val set_map0_tacs = map mk_single_set_map0_tac (0 upto num_inondead - 1);

    val set_alt_thms =
      if Config.get lthy quick_and_dirty then
        []
      else
        map (fn goal =>
          Goal.prove_sorry lthy [] [] goal
            (fn {context = ctxt, prems = _} =>
              mr_mk_comp_set_alt_tac ctxt (set_map_of_mrbnf outer) (var_types_of_mrbnf outer))
          |> Thm.close_derivation \<^here> )
        (map2 (curry mk_Trueprop_eq) sets sets_alt)
          |> (fn thms => cond_automap (fn thm => thm RS fun_cong) thms is_ilive);

    fun map_cong0_tac ctxt =
      mr_mk_comp_map_cong0_tac ctxt set'_eq_sets set_alt_thms (map map_cong0_of_mrbnf inners)
        outer ivar_types

    val set_bd_tacs = map (fn i => fn ctxt =>
      mr_mk_comp_set_bd_tac ctxt i (nth set'_eq_sets i) bd_ordIso_natLeq_thm_opt outer inners
    ) (0 upto num_inondead - 1);

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
           (rtac ctxt subset_UNIV)) 1)) ORELSE rtac ctxt subset_UNIV 1)
      );

    val (in_alt_thm, names_lthy) =
      let
        val (Asets, names_lthy) = mk_Frees "A" (map HOLogic.mk_setT As) names_lthy;
        val inx = mk_in Asets (cond_keep sets is_ilive) oT;
        val iterms = map2 (mk_in Asets) (map (fn xs => cond_keep xs is_ilive) inner_setss) iTs
        val in_alt = mk_in iterms (cond_keep outer_sets is_olive) oT;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        (Goal.prove_sorry lthy [] [] goal
          (fn {context = ctxt, prems = _} => mk_comp_in_alt_tac' ctxt set_alt_thms)
        |> Thm.close_derivation \<^here>,
        names_lthy)
      end;

    fun le_rel_OO_tac ctxt = mk_le_rel_OO_tac ctxt (le_rel_OO_of_mrbnf outer) (rel_mono_of_mrbnf outer)
      (map le_rel_OO_of_mrbnf inners)

    fun rel_OO_Grp_tac ctxt = mr_mk_rel_OO_Grp_tac ctxt set'_eq_sets in_alt_thm outer inners;

    fun pred_set_tac ctxt =
      let
        val pred_alt = unfold_thms ctxt @{thms Ball_Collect}
          (trans OF [pred_cong0_of_mrbnf outer OF map pred_set_of_mrbnf inners, pred_set_of_mrbnf outer]);
        val in_alt = case try (fn () => in_alt_thm RS @{thm Collect_inj} RS sym) () of
          SOME thm => thm
          | NONE => case try (fn () => trans OF [@{thm Set.UNIV_def} RS sym, in_alt_thm] RS @{thm Collect_inj} RS sym) () of
            SOME thm => Local_Defs.unfold0 ctxt @{thms Set.UNIV_def} thm
            | NONE => @{thm in_alt_top};
      in
        unfold_thms_tac ctxt (@{thm Ball_Collect} :: set'_eq_sets) THEN
        HEADGOAL (rtac ctxt (trans OF [pred_alt, in_alt]))
      end;

    val (wits, wit_tac, names_lthy) =
      let
        val num_owits = nwits_of_mrbnf outer;
        val (xs, names_lthy) = mk_Frees "x" As names_lthy;

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

        fun wit_tac ctxt = mr_mk_comp_wit_tac ctxt set'_eq_sets outer inners;
      in (wits, wit_tac, names_lthy) end;

    (* Define the map function of the composed MRBNF. It instantiates the map function of outer with the map functions of the inners:
     * \<forall>f1 ... fn v1 ... vm u1 ... ul. outer.map (inner_1.map f1 ... fn v1 ... vm u1 ... ul) ... (inner_m.map f1 ... fn v1 ... vm u1 ... ul) v1 ... vm u1 ... ul
     * Although in the example above the map function first takes all of the live variable functions, then all the bound variable function and
     * lastly the free variable functions, this does NOT have to be the case. Lives, bounds and frees can be interleaved in any order.
     * Additionally, the inners are only instanciated as the live variables of the outer, so the map function retains the functions for bounds and frees *)
    val (mapx, names_lthy) =
      let
        (* Create new variables for the different variable kinds and give them the types:
         *  - live: f1 ... fn : As\<^sub>i \<Rightarrow> As'\<^sub>i
         *  - bound: v1 ... vm : Bs\<^sub>j \<Rightarrow> Bs\<^sub>j
         *  - free: u1 ... ul : Fs\<^sub>k \<Rightarrow> Fs\<^sub>k *)
        val (((fs, vs), us), names_lthy) = names_lthy
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
        val body = Term.list_comb (mk_map_of_mrbnf oDs iTs iTs' Bs Fs outer, interlace_maps fn_bounds_frees_ids innermaps ovar_types)

      in (fold_rev Term.abs fn_vars body, names_lthy) end;

    (* The relator for the composed MRBNF just instantiates the variables of the outer relator with the relators of the inners
     * \<forall>Q1 ... Qn. outer.rel (inner1.rel Q1 ... Qn) ... (innerm.rel Q1 ... Qn)
     * The same happens for the predicator *)
    val (rel, pred, names_lthy) =
      let
        (* Invent new variable names for relator and predicator prop variables *)
        val ((Qs, Ps), names_lthy) = names_lthy
          |> apfst snd o BNF_Util.mk_Frees' "Q" (map2 BNF_Util.mk_pred2T As As')
          ||>> apfst snd o BNF_Util.mk_Frees' "P" (map BNF_Util.mk_pred1T As);
        (* Contrary to "map" the relator/predicator only works over the live variables, so no interlacing needed here *)
        fun mk_innerf f Ds inner = Term.list_comb (f Ds As As' Bs Fs inner, map Bound (num_ilives - 1 downto 0));
        fun mk_f f vars = fold_rev Term.abs vars (Term.list_comb (f oDs iTs iTs' Bs Fs outer, map2 (mk_innerf f) iDss inners))
      in (mk_f mk_rel_of_mrbnf Qs, mk_f (fn Ds => fn Ts => K (mk_pred_of_mrbnf Ds Ts)) Ps, names_lthy) end;

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

    val class_thms =
      let
        val ifco = bd_infinite_regular_card_order_of_mrbnf

        val var_goal = HOLogic.mk_UNIV (TFree (Name.aT, class))
          |> mk_card_of
          |> mk_ordLeq (mk_card_of (mk_Field bd'))
          |> HOLogic.mk_Trueprop;
        val large = #var_large o class_thms_of_mrbnf
        val var_thm = Goal.prove_sorry lthy [] [] var_goal (fn {context,...} =>
          mr_mk_bd_card_leq_UNIV_tac context (ifco outer) (map ifco inners)
            (large outer) (map large inners) bd_ordIso_natLeq_thm_opt
        ) |> Thm.close_derivation \<^here>;
        val (zs, _) = mk_Frees "z" (Fs @ Bs) lthy

        fun mk_covar_thm (coclass, lthy) =
          let
            val covar_goal = HOLogic.mk_UNIV (TFree (Name.aT, coclass))
              |> mk_card_of
              |> mk_ordLeq (BNF_LFP_Util.mk_cardSuc bd')
              |> HOLogic.mk_Trueprop;
            val large = #covar_large  o class_thms_of_mrbnf
          in Goal.prove_sorry lthy [] [] covar_goal (*(fold_rev Logic.all zs covar_goal)*) (fn {context,...} =>
            mr_mk_bd_cardSuc_leq_UNIV_tac context (ifco outer) (map ifco inners)
              (large outer) (map large inners) bd_ordIso_natLeq_thm_opt
          ) |> Thm.close_derivation \<^here> end;
      in ((class, var_thm, var_regular_of_mrbnf outer), (coclass, mk_covar_thm)) end;

    val (mrbnf, lthy') = mrbnf_def const_policy (K Dont_Note) true qualify tacs (SOME (oDs @ flat iDss)) (SOME class_thms)
              Binding.empty Binding.empty Binding.empty [] (((((((binding, oT), mapx), ivar_types ~~ sets'), bd'), wits), SOME rel), SOME pred) lthy

    val phi =
      Morphism.thm_morphism "MRBNF" (unfold_thms lthy' [id_mrbnf_def])
      $> Morphism.term_morphism "MRBNF" expand_id_mrbnf_def;

    val mrbnf' = morph_mrbnf phi mrbnf;
  in
    (mrbnf', (add_mrbnf_to_unfolds mrbnf' unfold_set, lthy'))
  end;

fun mk_simple_class_opt mrbnf =
  let
    val class_thms = class_thms_of_mrbnf mrbnf;
  in
    SOME (
      (class_of_mrbnf mrbnf, #var_large class_thms, #var_regular class_thms),
      (coclass_of_mrbnf mrbnf, K (#covar_large class_thms))
    )
  end;

(* Changing the order of live, free and bound variables *)
fun raw_permute_mrbnf qualify src dest mrbnf (accum as (unfold_set, lthy)) =
  if src = dest then (mrbnf, accum) else
  let
    val b = Binding.suffix_name (mk_permuteN src dest) (name_of_mrbnf mrbnf);

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

    val (((((Ds, As), As'), Fs), Bs), _) = lthy
      |> mk_TFrees' (map Type.sort_of_atyp deads)
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees' (map Type.sort_of_atyp frees)
      ||>> mk_TFrees' (map Type.sort_of_atyp bounds);

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
    val (ABFsets, _) = lthy
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

    (*Proof obligations*)
    fun map_id0_tac ctxt = rtac ctxt (map_id0_of_mrbnf mrbnf) 1;
    fun map_comp0_tac ctxt =
      rtac ctxt (map_comp0_of_mrbnf mrbnf) 1
      THEN ALLGOALS (assume_tac ctxt)

    fun map_cong0_tac ctxt = rtac ctxt (map_cong0_of_mrbnf mrbnf) 1
      THEN ALLGOALS (FIRST' [
        resolve_tac ctxt @{thms supp_id_bound bij_id},
        etac ctxt @{thm emptyE},
        assume_tac ctxt,
        Goal.assume_rule_tac ctxt
      ])
    val set_map0_tacs = permute (map (fn thm => fn ctxt =>
      HEADGOAL (rtac ctxt thm THEN_ALL_NEW assume_tac ctxt)) (set_map0_of_mrbnf mrbnf));
    fun bd_infinite_regular_card_order_tac ctxt = rtac ctxt (bd_infinite_regular_card_order_of_mrbnf mrbnf) 1;
    val set_bd_tacs = permute (map (fn thm => fn ctxt => rtac ctxt thm 1) (set_bd_of_mrbnf mrbnf));

    val in_alt_thm_opt =
      let
        val Asets = cond_keep ABFsets is_live_perm (*ABFsets are already permuted*)
        val inx = mk_in Asets (cond_keep sets is_live_perm) T;
        val in_alt = mk_in (unpermute_live Asets) (cond_keep mrbnf_sets is_live) T;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        if inx = in_alt then
          NONE
        else
          Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
            mk_permute_in_alt_tac ctxt src_live dest_live)
          |> Thm.close_derivation \<^here> |> SOME
      end;
    fun le_rel_OO_tac ctxt = rtac ctxt (le_rel_OO_of_mrbnf mrbnf) 1;

    fun rel_OO_Grp_tac ctxt =
      unfold_thms_tac ctxt (the_list in_alt_thm_opt) THEN
      rtac ctxt (rel_OO_Grp_of_mrbnf mrbnf) 1 THEN
      TRYALL (resolve_tac ctxt @{thms bij_id supp_id_bound} ORELSE' assume_tac ctxt)
    fun pred_set_tac ctxt = mr_mk_simple_pred_set_tac ctxt (pred_set_of_mrbnf mrbnf) in_alt_thm_opt

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
      mrbnf_def Smart_Inline (K Dont_Note) true qualify tacs (SOME Ds) (mk_simple_class_opt mrbnf)
        Binding.empty Binding.empty Binding.empty []
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

fun raw_demote_mrbnf qualify targetTs mrbnf (accum as (unfold_set, lthy)) =
  if targetTs = var_types_of_mrbnf mrbnf then (mrbnf, accum) else
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
    val ((Ds, As), names_lthy) = lthy
      |> mk_TFrees' (map Type.sort_of_atyp deads)
      ||>> mk_TFrees' (map (fn Live_Var => @{sort type} | Dead_Var => @{sort type} |_ => class) Atargets);

    val demotedAs = cond_keep As isdemot_A

    val (As', names_lthy) = let
      val (sAs', tlthy) = mk_TFrees new_live names_lthy;
    in (cond_interlace demotedAs sAs' isdemot_A, tlthy) end

    val ((Fs, Bs), names_lthy) = names_lthy
      |> mk_TFrees' (replicate free class)
      ||>> mk_TFrees' (replicate bound class);

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

    val ((Asets, lives), _) =
      let val still_lives = cond_keep As (map not isdemot_A) in names_lthy
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

    fun map_id0_tac ctxt = rtac ctxt (map_id0_of_mrbnf mrbnf) 1;
    fun map_comp0_tac ctxt = rtac ctxt trans 1  THEN
      rtac ctxt (map_comp0_of_mrbnf mrbnf) 2 THEN
      TRYALL (rtac ctxt @{thm supp_id_bound} ORELSE' rtac ctxt @{thm bij_id} ORELSE'
        assume_tac ctxt) THEN
      unfold_thms_tac ctxt @{thms id_comp} THEN
      rtac ctxt refl 1;

    fun map_cong0_tac ctxt =
      rtac ctxt (map_cong0_of_mrbnf mrbnf) 1
      THEN TRYALL (assume_tac ctxt)
      THEN TRYALL (Goal.assume_rule_tac ctxt)
      THEN TRYALL (rtac ctxt refl)
      THEN TRYALL (assume_tac ctxt)
      THEN TRYALL (rtac ctxt @{thm Prelim.supp_id_bound})
      THEN TRYALL (rtac ctxt @{thm Fun.bij_id});

    val set_map0_tacs = map (fn thm => fn ctxt => rtac ctxt thm 1
      THEN TRYALL (assume_tac ctxt) THEN TRYALL (rtac ctxt @{thm Prelim.supp_id_bound})
        THEN TRYALL (rtac ctxt @{thm Fun.bij_id}))
          (cond_keep (set_map0_of_mrbnf mrbnf) not_dead );

    fun bd_infinite_regular_card_order_tac ctxt = rtac ctxt (bd_infinite_regular_card_order_of_mrbnf mrbnf) 1;
    val set_bd_tacs = map (fn thm => fn ctxt => rtac ctxt thm 1)
      (cond_keep (set_bd_of_mrbnf mrbnf) not_dead);

    fun mr_kill_in_alt_tac ctxt = rtac ctxt refl 1 ORELSE (
      ((rtac ctxt @{thm Collect_cong} THEN' rtac ctxt iffI) 1 THEN
      REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
      REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE'
        rtac ctxt conjI THEN' rtac ctxt subset_UNIV) 1)) THEN
      (rtac ctxt subset_UNIV ORELSE' assume_tac ctxt) 1 THEN
      REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
      REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE' assume_tac ctxt) 1))) ORELSE
      ((rtac ctxt @{thm UNIV_eq_I} THEN' rtac ctxt CollectI) 1 THEN
        REPEAT_DETERM (TRY (rtac ctxt conjI 1) THEN rtac ctxt subset_UNIV 1)));

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
      unfold_thms_tac ctxt @{thms eq_OO} THEN rtac ctxt refl 1 ;

    fun rel_OO_Grp_tac ctxt =
      let
        val mr_rel_Grp = mr_rel_Grp_of_mrbnf mrbnf RS sym;
        val rel_cong0 = rel_cong0_of_mrbnf mrbnf;
        val rel_map = hd (rel_map_of_mrbnf mrbnf);
        val supp_bij_ass_tac = FIRST' [
          rtac ctxt @{thm supp_id_bound},
          rtac ctxt @{thm bij_id},
          assume_tac ctxt
        ];
        val fun_cong2_tac =
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            let
              val (x, y) = split_last (map snd params) |>> (snd o split_last)
              val thm = infer_instantiate' ctxt [NONE, NONE, SOME x, SOME y] @{thm fun_cong[OF fun_cong]}
            in rtac ctxt (thm RS trans) 1 end
          ) ctxt
      in
        EVERY1 [
          rtac ctxt sym,
          fun_cong2_tac,
          rtac ctxt (in_alt_thm RS @{thm OO_Grp_cong} RS trans),
          rtac ctxt @{thm arg_cong2[of _ _ _ _ "(OO)"]},
          rtac ctxt (@{thm arg_cong[of _ _ "conversep"]} RS trans),
          rtac ctxt mr_rel_Grp THEN_ALL_NEW supp_bij_ass_tac,
          rtac ctxt (mr_rel_conversep_of_mrbnf mrbnf RS sym) THEN_ALL_NEW supp_bij_ass_tac,
          rtac ctxt mr_rel_Grp THEN_ALL_NEW supp_bij_ass_tac,
          fun_cong2_tac,
          K (unfold_thms_tac ctxt @{thms inv_id}),
          rtac ctxt (mr_rel_OO_of_mrbnf mrbnf RS sym) THEN_ALL_NEW supp_bij_ass_tac,
          K (unfold_thms_tac ctxt @{thms o_id id_o Grp_fst_snd eq_alt[symmetric] conversep_eq eq_OO}),
          rtac ctxt trans,
          rtac ctxt (mr_rel_def_of_mrbnf mrbnf RS meta_eq_to_obj_eq |> BNF_Util.mk_unabs_def (live + free + bound + 2)),
          K (unfold_thms_tac ctxt @{thms Grp_UNIV_def}),
          rtac ctxt trans,
          rtac ctxt (rel_map RS sym),
          K (unfold_thms_tac ctxt @{thms id_def[symmetric]}),
          EqSubst.eqsubst_tac ctxt [0] [map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
          K (unfold_thms_tac ctxt @{thms id_o o_id}),
          rtac ctxt refl
        ]
      end;

    fun pred_set_tac ctxt = mk_simple_pred_set_tac ctxt (pred_set_of_mrbnf mrbnf) in_alt_thm;

    val mrbnf_wits = mk_wits_of_mrbnf (replicate nwits Ds) (replicate nwits As)
      (replicate nwits Bs) (replicate nwits Fs) mrbnf;

    val xs = cond_interlace (map (fn T => Const (@{const_name undefined}, T)) demotedAs) lives isdemot_A;
    val wits = map (fn t => fold absfree (Term.add_frees t []) t)
      (map (fn (I, wit) => Term.list_comb (wit, map (nth xs) I)) mrbnf_wits);

    fun wit_tac ctxt = mk_simple_wit_tac ctxt (wit_thms_of_mrbnf mrbnf);

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
      mrbnf_def Smart_Inline (K Dont_Note) true qualify tacs (SOME new_deads) (mk_simple_class_opt mrbnf)
        Binding.empty Binding.empty Binding.empty []
        (((((((b, T), mapx), var_type_sets), bd), wits), SOME rel), SOME pred) lthy;
  in
    (mrbnf', (add_mrbnf_to_unfolds mrbnf' unfold_set, lthy'))
  end;

fun demote_mrbnf qualify targetTs mrbnf (accum as ((cache, unfold_set), lthy)) =
  let val key = key_of_demote (cond_keep targetTs (map2 (curry op<>) targetTs (var_types_of_mrbnf mrbnf))) mrbnf in
    (case Typtab.lookup cache key of
      SOME (mrbnf, _) => (mrbnf, accum)
    | NONE => cache_comp_simple key cache (raw_demote_mrbnf qualify targetTs mrbnf (unfold_set, lthy)))
  end;

(* Adding dummy variables n1-Lives, n2-Frees, n3-Bounds *)

fun raw_lift_mrbnf qualify (n1, n2, n3) mrbnf (accum as (unfold_set, lthy)) =
  if n1 + n2 + n3 = 0 then (mrbnf, accum) else
  let
    (*Read out various attributes of the mrbnf via accessor methods*)
    val b = Binding.suffix_name (mk_liftN (n1, n2, n3)) (name_of_mrbnf mrbnf);
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
    val newcount = n1 + n2 + n3;

    (* TODO: check 0 < n, m < 0, l < 0 *)

    val (((((Ds, (newAs, As)), (newAs', As')), (newFs, Fs)), (newBs, Bs)), _) = lthy
      |> mk_TFrees' (map Type.sort_of_atyp deads)
      ||>> apfst (chop n1) o mk_TFrees (n1 + live)
      ||>> apfst (chop n1) o mk_TFrees (n1 + live)
      ||>> apfst (chop n2) o mk_TFrees' (replicate n2 class @ map Type.sort_of_atyp frees)
      ||>> apfst (chop n3) o mk_TFrees' (replicate n3 class @ map Type.sort_of_atyp bounds);

    val newVars = newAs @ newFs @ newBs
    val newVars' = newAs' @ newFs @ newBs

    val T = mk_T_of_mrbnf Ds As Bs Fs mrbnf;

    val mrbnf_sets = mk_sets_of_mrbnf (replicate count Ds) (replicate count As)
      (replicate count Bs) (replicate count Fs) mrbnf;
    val sets = map (fn A => absdummy T (HOLogic.mk_set A [])) newVars @ mrbnf_sets;
    val var_type_sets = (replicate n1 Live_Var @ replicate n2 Free_Var @  replicate n3 Bound_Var
      @ var_types_of_mrbnf mrbnf) ~~ sets;

    val (Asets, _) = lthy
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
    val bd = mk_bd_of_mrbnf Ds Bs Fs mrbnf;
    fun map_id0_tac ctxt = rtac ctxt (map_id0_of_mrbnf mrbnf) 1;
    fun map_comp0_tac ctxt = unfold_thms_tac ctxt (((map_comp0_of_mrbnf mrbnf RS sym)) ::
        @{thms comp_assoc id_comp comp_id}) THEN rtac ctxt refl 1 ;
    fun map_cong0_tac ctxt =
      rtac ctxt (map_cong0_of_mrbnf mrbnf) 1
      THEN REPEAT_DETERM_N (2 * (n2 + free + 2 * (n3 + bound))) (assume_tac ctxt 1)
      THEN REPEAT_DETERM_N (newcount + count) (Goal.assume_rule_tac ctxt 1);
    val set_map0_tacs =
      replicate newcount (fn ctxt => empty_natural_tac ctxt) @
        map (fn thm => fn ctxt => HEADGOAL (rtac ctxt thm THEN_ALL_NEW assume_tac ctxt)) (set_map0_of_mrbnf mrbnf);

    fun bd_infinite_regular_card_order_tac ctxt = rtac ctxt (bd_infinite_regular_card_order_of_mrbnf mrbnf) 1;
    val set_bd_tacs =
      replicate newcount (fn ctxt => HEADGOAL (rtac ctxt @{thm Cinfinite_gt_empty} THEN'
          rtac ctxt (bd_Cinfinite_of_mrbnf mrbnf))) @
        (map (fn thm => fn ctxt => rtac ctxt thm 1) (set_bd_of_mrbnf mrbnf));

    val in_alt_thm_opt =
      let
        fun flt_lives xs = cond_keep xs is_live;
        val live_sets = flt_lives Asets (*previously, Asets was used instead of live_sets*)
        val inx = mk_in live_sets (flt_lives sets) T;
        val in_alt = mk_in (drop n1 live_sets) (cond_keep mrbnf_sets (drop newcount is_live)) T;
        val goal = fold_rev Logic.all live_sets (mk_Trueprop_eq (inx, in_alt));
      in
        if inx = in_alt then
          NONE
        else
          Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} => lift_in_alt_tac ctxt)
          |> Thm.close_derivation \<^here> |> SOME
      end;

    fun le_rel_OO_tac ctxt = rtac ctxt (le_rel_OO_of_mrbnf mrbnf) 1;

    fun mr_mk_simple_rel_OO_Grp_tac ctxt rel_OO_Grp in_alt_thm =
      HEADGOAL (rtac ctxt (trans OF [rel_OO_Grp, in_alt_thm RS @{thm OO_Grp_cong} RS sym]));

    fun rel_OO_Grp_tac ctxt = unfold_thms_tac ctxt (the_list in_alt_thm_opt)
      THEN rtac ctxt (rel_OO_Grp_of_mrbnf mrbnf) 1
        THEN TRYALL (assume_tac ctxt);

    fun pred_set_tac ctxt = mr_mk_simple_pred_set_tac ctxt (pred_set_of_mrbnf mrbnf) in_alt_thm_opt;

    val wits = map snd (mk_wits_of_mrbnf (replicate nwits Ds) (replicate nwits As)
      (replicate nwits Bs) (replicate nwits Fs) mrbnf);

    fun wit_tac ctxt = mk_simple_wit_tac ctxt (wit_thms_of_mrbnf mrbnf);

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
      mrbnf_def Smart_Inline (K Dont_Note) true qualify tacs (SOME Ds) (mk_simple_class_opt mrbnf)
        Binding.empty Binding.empty Binding.empty []
        (((((((b, T), mapx), var_type_sets), bd), wits), SOME rel), SOME pred) lthy;

  in
    (mrbnf', (add_mrbnf_to_unfolds mrbnf' unfold_set, lthy'))
  end;

fun lift_mrbnf qualify ns mrbnf (accum as ((cache, unfold_set), lthy)) =
  let val key = key_of_lift ns mrbnf in
    (case Typtab.lookup cache key of
      SOME (mrbnf, _) => (mrbnf, accum)
    | NONE => cache_comp_simple key cache (raw_lift_mrbnf qualify ns mrbnf (unfold_set, lthy)))
  end;

(* Composition pipeline *)
fun lift_and_permute_mrbnf qualify ns src dest mrbnf =
  lift_mrbnf qualify ns mrbnf
  #> uncurry (permute_mrbnf qualify src dest);

fun tfree_ord ((a, S), (b, S')) = case fast_string_ord (a, b) of
  EQUAL => Term_Ord.sort_ord (S, S')
  | ord => ord
structure Vars = Table(type key = (string * sort) val ord = tfree_ord);

fun map_option f (SOME x) = SOME (f x)
  | map_option _ NONE = NONE

fun normalize_mrbnfs qualify oAs Ass Ds Xs flatten_tyargs outer_opt mrbnfs accum =
  let
    val oAs' = case outer_opt of
      NONE => []
      | SOME outer => map_filter (fn (x, var_type) => case x of
        SOME y => SOME (y, var_type)
        | NONE => NONE
      ) (oAs ~~ var_types_of_mrbnf outer);
    val var_map = fold (fold (fn (A, var_type) => Vars.map_default (A, var_type) (fn var_type' =>
      case var_type_ord (var_type, var_type') of LESS => var_type | _ => var_type'
    ))) (oAs' :: Xs :: map2 (fn As => fn mrbnf => As ~~ var_types_of_mrbnf mrbnf) Ass mrbnfs)
      (Vars.make (Ds ~~ replicate (length Ds) MRBNF_Def.Dead_Var))

    val odemote_target_types = map (fn x => case x of
      SOME y => the (Vars.lookup var_map y)
      | NONE => Live_Var
    ) oAs;
    val (outer_opt', accum') = case outer_opt of
      NONE => (outer_opt, accum)
      | SOME outer => apfst SOME (demote_mrbnf (qualify 0) odemote_target_types outer accum)

    val demote_target_types = map (map_filter (fn A => Vars.lookup var_map A)) Ass
    val (inners', accum'') = @{fold_map 3} (demote_mrbnf o qualify)
      (1 upto length mrbnfs) demote_target_types mrbnfs accum'

    val oAs2 = filter (fn SOME A =>
      let val var_type = the (Vars.lookup var_map A)
      in case var_type of
        Dead_Var => false | _ => true
      end
    | NONE => true) oAs
    fun map_filter_killed f = map_filter (fn A => case Vars.lookup var_map A of
      SOME Dead_Var => NONE | SOME x => SOME (f A x) | NONE => SOME (f A Live_Var)
    );
    val As = map_filter_killed pair (flatten_tyargs (map fst oAs' :: Ass))
    fun get_lifts vars = sort (fn (a, b) => var_type_ord (snd b, snd a)) (subtract (fn (a, b) => a = fst b) vars As)
    fun count_lifts As = fold (fn (_, var_type) => fn (n1, n2, n3) => case var_type of
      MRBNF_Def.Live_Var => (n1 + 1, n2, n3)
      | MRBNF_Def.Free_Var => (n1, n2 + 1, n3)
      | MRBNF_Def.Bound_Var => (n1, n2, n3 + 1)
      | MRBNF_Def.Dead_Var => (n1, n2, n3)
    ) As (0, 0, 0)

    val Ass' = map (map_filter_killed K) Ass
    val kill_poss = map (map_filter I o map_index (fn (i, A) => case the (Vars.lookup var_map A) of
      Dead_Var => SOME i | _ => NONE
    )) Ass
    val new_oDs = map_filter I (map_index (fn (i, x) => case x of
      SOME y => (case the (Vars.lookup var_map y) of
        Dead_Var => SOME i | _ => NONE)
      | _ => NONE
    ) oAs)
    val need_liftss = map get_lifts Ass'
    val lift_ns = map count_lifts need_liftss
    val dests = replicate (length Ass') (0 upto length As - 1)
    val find_indices' = map (fn x => find_index (equal x) (map fst As))
    val srcs = map find_indices' (map2 (append o map fst) need_liftss Ass')

    val oneed_lifts = filter (fn (_, var_type) => var_type <> MRBNF_Def.Live_Var) (get_lifts (map fst oAs'))
    val olift_ns = count_lifts oneed_lifts
    val odest = 0 upto length oAs2 + length oneed_lifts - 1
    val osrc =
      let
        val vars = map (SOME o fst) oneed_lifts @ oAs2
        val As' = map_filter (fn (var, var_type) =>
          if var_type = MRBNF_Def.Free_Var orelse var_type = MRBNF_Def.Bound_Var then
            SOME var
          else
            NONE
        ) As
      in fold_rev (fn x => fn (xs, ys) => case x of
        SOME var => (find_index (equal var) As'::xs, ys)
        | NONE => (hd ys::xs, tl ys)
      ) vars ([], length vars - 1 downto length As') |> fst
      end

    val (outer_opt'', accum''') = case outer_opt' of
      NONE => (outer_opt', accum'')
      | SOME outer' => apfst SOME (lift_and_permute_mrbnf (qualify (length mrbnfs)) olift_ns osrc odest outer' accum'')
  in
    ((kill_poss, map fst As),
      outer_opt'',
      @{fold_map 5} (lift_and_permute_mrbnf o qualify)
        (if length mrbnfs = 1 then [0] else 1 upto length mrbnfs)
        lift_ns srcs dests inners' accum''')
  end;

fun raw_compose_mrbnf const_policy qualify flatten_tyargs outer inners oDs Dss otfrees tfreess Xs accum =
  let
    val b = name_of_mrbnf outer;
    val Ass = map (map Term.dest_TFree) tfreess;
    val oAs = map (map_option Term.dest_TFree) otfrees
    val Ds = fold (fold Term.add_tfreesT) (oDs :: Dss) [];
    val ((kill_poss, As), outer', (inners', ((cache', unfold_set'), lthy'))) =
      normalize_mrbnfs qualify oAs Ass Ds Xs flatten_tyargs (SOME outer) inners accum;
    val Ds =
      oDs @ flat (@{map 3} (uncurry append oo curry swap oo map o nth) tfreess kill_poss Dss);
    val As = map TFree As;
  in
    apfst (rpair (Ds, As))
      (apsnd (apfst (pair cache'))
        (clean_compose_mrbnf const_policy (qualify 0) b (the outer') inners' (unfold_set', lthy')))
  end;

fun compose_mrbnf const_policy qualify flatten_tyargs outer inners oDs Dss otfrees tfreess Xs
    (accum as ((cache, _), _)) =
  let val key = key_of_compose oDs Dss (map_filter I otfrees) tfreess outer inners in
    (case Typtab.lookup cache key of
      SOME mrbnf_Ds_As => (mrbnf_Ds_As, accum)
    | NONE =>
      cache_comp key
        (raw_compose_mrbnf const_policy qualify flatten_tyargs outer inners oDs Dss otfrees tfreess Xs accum))
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
fun mk_abs_or_rep _ absU (Const (@{const_name BNF_Composition.id_bnf}, _)) =
    Const (@{const_name BNF_Composition.id_bnf}, absU --> absU)
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
        (@{const_name BNF_Composition.id_bnf}, @{const_name BNF_Composition.id_bnf},
         @{thm BNF_Composition.type_definition_id_bnf_UNIV},
         @{thm type_definition.Abs_inverse[OF BNF_Composition.type_definition_id_bnf_UNIV]},
         @{thm type_definition.Abs_inject[OF BNF_Composition.type_definition_id_bnf_UNIV]},
         @{thm type_definition.Abs_cases[OF BNF_Composition.type_definition_id_bnf_UNIV]})), lthy)
  end;

fun seal_mrbnf qualify (unfold_set : unfold_set) b force_out_of_line Ds all_Ds mrbnf lthy =
  let
    val live = live_of_mrbnf mrbnf;
    val frees = frees_of_mrbnf mrbnf;
    val bounds = bounds_of_mrbnf mrbnf;
    val nwits = nwits_of_mrbnf mrbnf;
    val nondead = live + length bounds + length frees;
    val var_types = var_types_of_mrbnf mrbnf;
    val ((As, As'), lthy1) = apfst (`(map TFree))
      (Variable.invent_types (replicate live @{sort type}) (fold Variable.declare_typ all_Ds lthy));
    val (Xs, lthy2) = apfst (map TFree) (Variable.invent_types (replicate live @{sort type}) lthy1);
    val (Bs, lthy3) = apfst (map TFree) (Variable.invent_types (map (snd o Term.dest_TVar) bounds) lthy2);
    val (Fs, lthy4) = apfst (map TFree) (Variable.invent_types (map (snd o Term.dest_TVar) frees) lthy3);
    val ((((fs, fs'), (Rs, Rs')), (Ps, Ps')), _(*names_lthy*)) = lthy
      |> mk_Frees' "f" (map2 (curry op -->) (interlace As Bs Fs var_types) (interlace Xs Bs Fs var_types))
      ||>> mk_Frees' "R" (map2 mk_pred2T As Xs)
      ||>> mk_Frees' "P" (map mk_pred1T As);
    val repTA = mk_T_of_mrbnf Ds As Bs Fs mrbnf;
    val T_bind = qualify b;
    val repTA_tfrees = Term.add_tfreesT repTA [];
    val all_TA_params_in_order = fold_rev Term.add_tfreesT all_Ds (interlace As' (map dest_TFree Bs) (map dest_TFree Fs) var_types);
    val TA_params =
      (if force_out_of_line then all_TA_params_in_order
       else inter (op =) repTA_tfrees all_TA_params_in_order);
    val ((TA, (Rep_name, Abs_name, type_definition, Abs_inverse, Abs_inject, _)), lthy) =
      maybe_typedef force_out_of_line (T_bind, TA_params, NoSyn) (HOLogic.mk_UNIV repTA) NONE
        (fn ctxt => EVERY' [rtac ctxt exI, rtac ctxt UNIV_I] 1) lthy;
    val repTB = mk_T_of_mrbnf Ds Xs Bs Fs mrbnf;
    val TB = Term.typ_subst_atomic (As ~~ Xs) TA;
    val RepA = Const (Rep_name, TA --> repTA);
    val RepB = Const (Rep_name, TB --> repTB);
    val AbsA = Const (Abs_name, repTA --> TA);
    val AbsB = Const (Abs_name, repTB --> TB);
    val Abs_inject' = Abs_inject OF @{thms UNIV_I UNIV_I};
    val Abs_inverse' = Abs_inverse OF @{thms UNIV_I};
    val absT_info = {absT = TA, repT = repTA, abs = AbsA, rep = RepA, abs_inject = Abs_inject',
      abs_inverse = Abs_inverse', type_definition = type_definition};
    val mrbnf_map = fold_rev Term.absfree fs' (HOLogic.mk_comp (HOLogic.mk_comp (AbsB,
      Term.list_comb (mk_map_of_mrbnf Ds As Xs Bs Fs mrbnf, fs)), RepA));
    val mrbnf_sets = (var_types_of_mrbnf mrbnf ~~ map ((fn t => HOLogic.mk_comp (t, RepA)))
      (mk_sets_of_mrbnf (replicate nondead Ds) (replicate nondead As) (replicate nondead Bs) (replicate nondead Fs) mrbnf));
    val mrbnf_bd = mk_bd_of_mrbnf Ds Bs Fs mrbnf;
    val mrbnf_rel = fold_rev Term.absfree Rs' (mk_vimage2p RepA RepB $
      (Term.list_comb (mk_rel_of_mrbnf Ds As Xs Bs Fs mrbnf, Rs)));
    val mrbnf_pred = fold_rev Term.absfree Ps' (HOLogic.mk_comp
      (Term.list_comb (mk_pred_of_mrbnf Ds As Bs Fs mrbnf, Ps), RepA));
    (*bd may depend only on dead type variables*)
    val bd_repT = fst (dest_relT (fastype_of mrbnf_bd));
    val bdT_bind = qualify (Binding.suffix_name ("_" ^ bdTN) b);
    val params = Term.add_tfreesT bd_repT [];
    val all_deads = map TFree (fold_rev Term.add_tfreesT all_Ds []);
    val ((bdT, (_, Abs_bd_name, _, _, Abs_bdT_inject, Abs_bdT_cases)), lthy) =
      maybe_typedef false (bdT_bind, params, NoSyn) (HOLogic.mk_UNIV bd_repT) NONE
        (fn ctxt => EVERY' [rtac ctxt exI, rtac ctxt UNIV_I] 1) lthy;
    val (mrbnf_bd', bd_ordIso, bd_infinite_regular_card_order) =
      if bdT = bd_repT then (mrbnf_bd, bd_Card_order_of_mrbnf mrbnf RS @{thm ordIso_refl},
        bd_infinite_regular_card_order_of_mrbnf mrbnf)
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
          val bd_regularCard = @{thm regularCard_ordIso} OF [bd_ordIso, bd_Cinfinite_of_mrbnf mrbnf, bd_regularCard_of_mrbnf mrbnf]
          val bd_infinite_regular_card_order = @{thm infinite_regular_card_order.intro} OF [
            bd_card_order, bd_cinfinite, bd_regularCard
          ]
        in
          (mrbnf_bd', bd_ordIso, bd_infinite_regular_card_order)
        end;
    fun map_id0_tac ctxt =
      rtac ctxt (@{thm type_copy_map_id0} OF [type_definition, map_id0_of_mrbnf mrbnf]) 1;
    fun map_comp0_tac ctxt = HEADGOAL (
      rtac ctxt (@{thm type_copy_map_comp0} OF [type_definition, map_comp0_of_mrbnf mrbnf])
      THEN_ALL_NEW (assume_tac ctxt));
    fun map_cong0_tac ctxt =
      EVERY1 [
        rtac ctxt @{thm type_copy_map_cong0},
        rtac ctxt (map_cong0_of_mrbnf mrbnf),
        K (unfold_thms_tac ctxt @{thms o_apply})
      ] THEN ALLGOALS (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt);
    fun set_map0_tac thm ctxt = HEADGOAL (
      rtac ctxt (@{thm type_copy_set_map0} OF [type_definition, thm]) THEN_ALL_NEW
        (assume_tac ctxt));
    val set_bd_tacs = map (fn thm => fn ctxt =>
      rtac ctxt (@{thm ordLess_ordIso_trans} OF [thm, bd_ordIso] RS @{thm type_copy_set_bd}) 1
    ) (set_bd_of_mrbnf mrbnf);
    fun le_rel_OO_tac ctxt =
      rtac ctxt (le_rel_OO_of_mrbnf mrbnf RS @{thm vimage2p_relcompp_mono}) 1;
    fun rel_OO_Grp_tac ctxt =
      unfold_thms_tac ctxt (Abs_inverse' :: @{thms vimage2p_def o_apply}) THEN
      EVERY1 [
        Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
          let
            val ((fs, Rs), _) = params
              |> chop (bound_of_mrbnf mrbnf + free_of_mrbnf mrbnf)
              ||>> chop (live_of_mrbnf mrbnf)
            val thm = infer_instantiate' ctxt (
              map (SOME o snd) (fs @ Rs)
            ) (rel_OO_Grp_of_mrbnf mrbnf RS sym);
          in rtac ctxt (trans OF [thm RS sym]) 1 end
        ) ctxt,
        REPEAT_DETERM o assume_tac ctxt,
        rtac ctxt (trans OF [@{thm Grp_Rep} OF [type_definition, type_definition]]),
        Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
          let
            val (params', (_, y)) = split_last params
            val (_, (_, x)) = split_last params'
            val thm = infer_instantiate' context [NONE, NONE, SOME x, SOME y] (fun_cong RS fun_cong)
          in rtac context thm 1 end
        ) ctxt,
        rtac ctxt (trans OF @{thms OO_cong}),
        rtac ctxt @{thm conversep_cong},
        rtac ctxt (@{thm type_copy_vimage2p_Grp_Rep_id} OF [type_definition] RS sym),
        rtac ctxt (@{thm type_copy_vimage2p_Grp_Rep_id} OF [type_definition] RS sym),
        rtac ctxt (trans OF [@{thm vimage2p_relcompp_converse} OF @{thms type_definition_id} RS sym]),
        rtac ctxt sym,
        rtac ctxt (trans OF @{thms OO_cong}),
        rtac ctxt @{thm conversep_cong},
        rtac ctxt (@{thm type_copy_vimage2p_Grp_Rep} OF [type_definition] RS sym),
        rtac ctxt (@{thm type_copy_vimage2p_Grp_Rep} OF [type_definition] RS sym),
        rtac ctxt (trans OF [@{thm vimage2p_relcompp_converse} OF [type_definition] RS sym]),
        rtac ctxt refl
      ];
    fun pred_set_tac ctxt =
      HEADGOAL (EVERY'
        [rtac ctxt (pred_set_of_mrbnf mrbnf RS @{thm arg_cong[of _ _ "\<lambda>f. f \<circ> _"]} RS trans),
        SELECT_GOAL (unfold_thms_tac ctxt (@{thms Ball_comp_iff conj_comp_iff})), rtac ctxt refl]);
    val mrbnf_wits = map (fn (I, t) =>
      fold Term.absdummy (map (nth As) I)
        (AbsA $ Term.list_comb (t, map Bound (0 upto length I - 1))))
      (mk_wits_of_mrbnf (replicate nwits Ds) (replicate nwits As) (replicate nwits Bs) (replicate nwits Fs) mrbnf);
    fun bd_infinite_regular_card_order_tac ctxt = rtac ctxt bd_infinite_regular_card_order 1
    fun wit_tac ctxt =
      ALLGOALS (dtac ctxt (type_definition RS @{thm type_copy_wit})) THEN
      mk_simple_wit_tac ctxt (wit_thms_of_mrbnf mrbnf);

    val tacs = {
      map_id0 = map_id0_tac,
      map_comp0 = map_comp0_tac,
      map_cong0 = map_cong0_tac,
      set_map0 = map set_map0_tac (set_map0_of_mrbnf mrbnf),
      infinite_regular_card_order = bd_infinite_regular_card_order_tac,
      set_bd = set_bd_tacs,
      le_rel_OO = le_rel_OO_tac,
      in_rel = rel_OO_Grp_tac,
      pred_set = pred_set_tac,
      wit = wit_tac
    };

    fun mk_class prfx xs f lthy =
      (Class_Declaration.class (qualify (Binding.name (prfx ^ Binding.name_of b))) [] xs [] #>> single ##> f ##> Local_Theory.exit_global |> Local_Theory.background_theory_result) lthy
    val (class, lthy3) = mk_class "var_" (class_of_mrbnf mrbnf) I lthy;

    val class_thms = class_thms_of_mrbnf mrbnf;
    val covar_large' = @{thm ordIso_ordLeq_trans} OF [
      @{thm cardSuc_invar_ordIso[THEN iffD2]} OF [
        @{thm infinite_regular_card_order.Card_order} OF [bd_infinite_regular_card_order],
        @{thm infinite_regular_card_order.Card_order} OF [bd_infinite_regular_card_order_of_mrbnf mrbnf],
        @{thm ordIso_symmetric} OF [bd_ordIso]
      ],
      #covar_large class_thms
    ]
    val (coclass, lthy) = mk_class "covar_" (coclass_of_mrbnf mrbnf) (fn ctxt =>
      let val subclass_tac = Locale.intro_locales_tac {strict = true, eager = true} ctxt []
      in Class_Declaration.prove_subclass subclass_tac (the_single class) ctxt end
    ) lthy3;

    val class_thms =
      let
        val var_large' = @{thm ordIso_ordLeq_trans} OF [
          @{thm card_of_cong} OF [@{thm ordIso_symmetric} OF [bd_ordIso]],
          #var_large class_thms
        ]
      in
        (
          (class, var_large', #var_regular class_thms),
          (coclass, K covar_large')
        )
      end

    val (mrbnf', lthy') =
      mrbnf_def Hardly_Inline (user_policy Note_Some) true qualify tacs (SOME all_deads) (SOME class_thms)
        Binding.empty Binding.empty Binding.empty []
        (((((((b, TA), mrbnf_map), mrbnf_sets), mrbnf_bd'), mrbnf_wits), SOME mrbnf_rel), SOME mrbnf_pred) lthy;
    val unfolds = @{thm id_bnf_apply} ::
      (#map_unfolds unfold_set @ flat (#set_unfoldss unfold_set) @ #rel_unfolds unfold_set);
    val mrbnf'' = mrbnf' |> morph_mrbnf_defs (Morphism.thm_morphism "MRBNF" (unfold_thms lthy' unfolds));
    val map_def = map_def_of_mrbnf mrbnf'';
    val set_defs = set_defs_of_mrbnf mrbnf'';
    val rel_def = rel_def_of_mrbnf mrbnf'';
    val mrbnf_b = qualify b;
    val def_qualify =
      Thm.def_binding o Binding.concealed o Binding.qualify false (Binding.name_of mrbnf_b);
    fun mk_prefix_binding pre = Binding.prefix_name (pre ^ "_") mrbnf_b;
    val map_b = def_qualify (mk_prefix_binding mapN);
    val rel_b = def_qualify (mk_prefix_binding relN);
    val set_bs = if nondead = 1 then [def_qualify (mk_prefix_binding setN)]
      else map (def_qualify o mk_prefix_binding o mk_setN) (1 upto nondead);
    val notes = (map_b, map_def) :: (rel_b, rel_def) :: (set_bs ~~ set_defs)
      |> map (fn (b, def) => ((b, []), [([def], [])]))
    val (noted, lthy'') = lthy'
      |> Local_Theory.notes notes
      ||> (if repTA = TA then I else register_mrbnf_raw (fst (dest_Type TA)) mrbnf'')
  in
    ((morph_mrbnf (substitute_noted_thm noted) mrbnf'', (all_deads, absT_info)), lthy'')
  end;

exception BAD_DEAD of typ * typ;
fun mrbnf_of_typ _ _ qualify _ _ Ds0 var_types (T as TFree T') accum =
    (if member (op =) Ds0 T' then ((DEADID_mrbnf, ([T], [])), accum) else
      (case map_filter (fn a => if fst a = T' then SOME (snd a) else NONE) var_types of
        [] => ((ID_mrbnf, ([], [T])), accum)
        | [Dead_Var] => error "var_types may only be Live, Free or Bound, use Ds0 for deads"
        | [var_type] => let
                          val qualify' = qualify o Binding.suffix_name ("_" ^ fst T')
                          val (ID', accum') = demote_mrbnf qualify' [var_type] ID_mrbnf accum
                        in ((ID', ([], [T])), accum') end
        | _ => error "Same variable appears twice in var_types"
      )
    )
  | mrbnf_of_typ _ _ _ _ _ _ _ (TVar _) _ = error "Unexpected schematic variable"
  | mrbnf_of_typ optim const_policy qualify' flatten_tyargs Xs Ds0 var_types (T as Type (C, Ts))
      (accum as (x, lthy)) =
    let
      fun check_bad_dead ((_, (deads, _)), _) =
        let val Ds = fold Term.add_tfreesT deads [] in
          (case Library.inter (op =) Ds Xs of [] => ()
          | X :: _ => raise BAD_DEAD (TFree X, T))
        end;
      val tfrees = subtract (op =) Ds0 (Term.add_tfreesT T []);
      val mrbnf_opt = if null tfrees then NONE else
        case mrbnf_of lthy C of
          SOME mrbnf => SOME (mrbnf, lthy)
          | NONE => case BNF_Def.bnf_of lthy C of
            SOME bnf => SOME (register_bnf_as_mrbnf NONE bnf lthy)
            | NONE => NONE;
    in
      (case mrbnf_opt of
        NONE => ((DEADID_mrbnf, ([T], [])), accum)
      | SOME (mrbnf, lthy') =>
        if forall (can Term.dest_TFree) Ts andalso length Ts = length tfrees
          andalso Library.inter (fn (a, b) => fst a = fst b andalso snd a <> snd b)
            (map dest_TFree Ts ~~ var_types_of_mrbnf mrbnf) var_types = []
        then
          let
            val T' = T_of_mrbnf mrbnf;
            val deads = deads_of_mrbnf mrbnf;
            val frees = frees_of_mrbnf mrbnf;
            val bounds = bounds_of_mrbnf mrbnf;
            val lives = lives_of_mrbnf mrbnf;
            val vars = interlace lives bounds frees (var_types_of_mrbnf mrbnf)
            val tvars' = Term.add_tvarsT T' [];
            val Ds_As =
              apply2 (map (Term.typ_subst_TVars (map fst tvars' ~~ map TFree tfrees)))
                (deads, vars);
          in ((mrbnf, Ds_As), (x, lthy')) end
        else
          let
            val name = Long_Name.base_name C;
            fun qualify i =
              let val namei = name ^ nonzero_string_of_int i;
              in qualify' o Binding.qualify true namei end;
            val odead = dead_of_mrbnf mrbnf;
            val olive = live_of_mrbnf mrbnf;
            val obound = bound_of_mrbnf mrbnf;
            val ofree = free_of_mrbnf mrbnf;
            val Ds = map (fn i => TFree (string_of_int i, [])) (1 upto odead);
            val Us = snd (Term.dest_Type (mk_T_of_mrbnf Ds (replicate olive dummyT) (replicate obound dummyT) (replicate ofree dummyT) mrbnf));
            val oDs_pos = map (fn x => find_index (fn y => x = y) Us) Ds
              |> filter (fn x => x >= 0);
            val oAs = map (fn (T, var_type) => case var_type of
              Live_Var => NONE | _ => SOME T
            ) (Ts ~~ var_types_of_mrbnf mrbnf)
            val oDs = map (nth Ts) oDs_pos;
            val ofree_bound_pos = map_filter I (map_index (fn (i, x) => case x of
              SOME _ => SOME i | NONE => NONE
            ) oAs)
            val Ts' = map (nth Ts) (subtract (op =) (oDs_pos @ ofree_bound_pos) (0 upto length Ts - 1));
            val ((inners, (Dss, Ass)), (accum', lthy'')) =
              apfst (apsnd split_list o split_list) (@{fold_map 2}
                (fn i => mrbnf_of_typ optim Smart_Inline (qualify i) flatten_tyargs Xs Ds0 var_types)
                (if length Ts' = 1 then [0] else 1 upto length Ts') Ts' (x, lthy'));
            val Xs' = map (swap o `(the_default MRBNF_Def.Live_Var o AList.lookup (op=) var_types)) Xs
          in
            compose_mrbnf const_policy qualify flatten_tyargs mrbnf inners oDs Dss oAs Ass Xs' (accum', lthy'')
          end)
      |> tap check_bad_dead
    end;

end;
