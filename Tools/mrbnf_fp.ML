signature MRBNF_FP =
sig
  val construct_binder_fp: BNF_Util.fp_kind -> ((string * MRBNF_Def.mrbnf) * int) list ->
    int list list -> local_theory -> MRBNF_FP_Def_Sugar.fp_result list * local_theory
end;

structure MRBNF_FP : MRBNF_FP =
struct

open MRBNF_Util
open MRBNF_Def
open MRBNF_Fp_Tactics
open MRBNF_FP_Def_Sugar

val mk_TN = prefix "raw_";
val mk_ctorN = suffix "_ctor" o prefix "raw_";
val mk_renameN = prefix "rename_";
fun mk_freeN i = prefix "free_" o suffix (nonzero_string_of_int i);
fun mk_set_levelN i = prefix ("set" ^ nonzero_string_of_int i ^ "_") o suffix "_level" o
  foldr1 (fn (s1, s2) => s1 ^ "_" ^ s2);
fun mk_FVarsN i = prefix "FVars_" o suffix (nonzero_string_of_int i);
val mk_alphaN = prefix "alpha_";
val mk_avoidN = prefix "avoid_";
val mk_cctorN = suffix "_ctor";
val mk_rrenameN = prefix "rrename_";
fun mk_FFVarsN i = prefix "FFVars_" o suffix (nonzero_string_of_int i);
val mk_aavoidN = prefix "aavoid_";
val mk_subshapeN = prefix "subshape_" oo prefix o suffix "_";
val mk_alpha'N = prefix "alpha'_";

val mk_minus = HOLogic.mk_binop @{const_name minus} |> curry;

val mk_inter = HOLogic.mk_binop @{const_name inf};

fun mk_equivp t = Const (@{const_name equivp}, mk_predT [fastype_of t]) $ t;

fun mk_Sigma (A, B) =
  let
    val AT = fastype_of A;
    val BT = fastype_of B;
    val ABT = mk_relT (HOLogic.dest_setT AT, HOLogic.dest_setT (range_type BT));
  in Const (@{const_name Sigma}, AT --> BT --> ABT) $ A $ B end;

fun mk_Sigma_prod (A, B) =
  let
    val T = fastype_of A |> HOLogic.dest_setT;
  in mk_Sigma (A, absdummy T B) end;

fun fold_case_prod vs t =
  let
    fun fold_case_prod' [] t = t
      | fold_case_prod' [v] t = absfree v t
      | fold_case_prod' [v1, v2] t = absfree v2 t |> absfree v1 |> HOLogic.mk_case_prod
      | fold_case_prod' (v :: vs) t = absfree v (fold_case_prod' vs t) |> HOLogic.mk_case_prod;
  in
    fold_case_prod' (map dest_Free vs) t
  end;

fun mk_bound t = t
  |> fastype_of
  |> HOLogic.dest_setT
  |> HOLogic.mk_UNIV
  |> mk_card_of
  |> mk_ordLess (mk_card_of t);

fun mk_sumN_balanced ts i = BNF_FP_Util.mk_sumprod_balanced
  (BNF_FP_Util.mk_sumTN_balanced (map fastype_of ts)) (length ts) i [nth ts (i-1)];

val mk_case_sumN_balanced = Balanced_Tree.make BNF_FP_Util.mk_case_sum;

fun primrec int fixes specs lthy: (term list * thm list * thm list list) * local_theory =
  let
    val ((_, (terms, defs, (_, simpss))), lthy) =
      BNF_LFP_Rec_Sugar.primrec_simple int fixes specs lthy;
  in
    ((terms, defs, simpss), lthy)
  end;

fun primcorec int fixes specs lthy: (term list * thm list * thm list list) * local_theory =
  let
    val decl = fixes |> Free o apfst Binding.name_of o fst o hd;
    val specs' = map (pair (Binding.empty, [])) specs;
  in
    BNF_GFP_Rec_Sugar.primcorec_ursive int true [] fixes specs' (replicate (length specs) NONE) lthy
    |> (fn (goalss, after_qed, lthy) => lthy
      |> after_qed (map (fn [] => [] | _ => error "\"auto\" failed") goalss))
    |> `(fn lthy: local_theory => Spec_Rules.retrieve lthy decl
      |> hd
      |> (fn spec => (#terms spec, [], map single (#rules spec))))
  end;

fun define_raw_terms co names mrbnfs ks binding_relation lthy =
  let
    (* Get mrbnf info *)
    val (frees, free_sortss) = map_split
      (`length o map (dest_TVar #> snd) o frees_of_mrbnf) mrbnfs;
    val (bounds, bound_sortss) = map_split
      (`length o map (dest_TVar #> snd) o bounds_of_mrbnf) mrbnfs;
    val lives = map (length o lives_of_mrbnf) mrbnfs;
    val Fs = map (fst o dest_Type o T_of_mrbnf) mrbnfs;

    (* Error checking *)
    fun all_equal [] _ = raise List.Empty
      | all_equal (x :: xs) msg = if List.all (curry op = x) xs then x else error msg;
    val free = all_equal frees "Number of free types must be equal";
    val bound = all_equal bounds "Number of bound types must be equal";
    val live = all_equal lives "Number of live types must be equal";
    val _ = if length ks = 1 orelse List.all (curry op < 0) ks then
        if length ks > 1 orelse (hd ks >= 0) then () else
        error "All ks must not be negative" else
      error "All ks must be at least one";
    val k_sum = foldr1 op+ ks;
    val _ = if live >= k_sum then () else
      error "Sum of ks must not exceed number of live types";
    val bound_bounds = (length o filter I oo map o List.exists)
      (fn i => 0 <= i andalso i <= k_sum-1) binding_relation;
    val _ = if bound_bounds >= 1 then () else
      error "Need at least one binding";
    val _ = if bound_bounds <= free then () else
      error "Not enough free types";
    val _ = if bound_bounds <= bound then () else
      error "Not enough bound types";
    val sort : sort = distinct op = (if co
      then maps coclass_of_mrbnf mrbnfs
      else all_equal (transpose free_sortss @ transpose bound_sortss)
        "Sorts of free and bound types must be equal" |> flat);
    val f_sorts = replicate free sort;
    val b_sorts = replicate (bound-bound_bounds) sort;

    (* Make names and construct groups *)
    val bs = map (Binding.name o mk_TN) names;
    val TNs = map (Local_Theory.full_name lthy) bs;
    val ctorNs = map mk_ctorN names;
    val frees_lives = mk_TFrees' f_sorts lthy ||>> mk_TFrees (live - k_sum) |>> op @
      ||> fst o mk_TFrees' b_sorts |> op @;
    fun mk_T_group TN k = Type (TN, frees_lives) |> replicate k;
    val T_groups = frees_lives @ take bound_bounds frees_lives @
      List.concat (map2 mk_T_group TNs ks);
    val T_Ts = map (`dest_TFree #>> snd #> swap #> pair NONE) frees_lives;

    (* Build spec *)
    fun mk_T_spec b = ((T_Ts, b), NoSyn);
    fun mk_ctor_spec F ctorN = (((Binding.empty, Binding.name ctorN),
      single (Binding.empty, Type (F, T_groups))), NoSyn);
    fun mk_T_specs F b ctorN = (((mk_T_spec b, mk_ctor_spec F ctorN |> single),
      (Binding.empty, Binding.empty, Binding.empty)), []);
    val T_specs = @{map 3} mk_T_specs Fs bs ctorNs;

    (* Define co-datatype *)
    val lthy = (if co
      then BNF_FP_Def_Sugar.co_datatypes Greatest_FP BNF_GFP.construct_gfp
      else BNF_FP_Def_Sugar.co_datatypes Least_FP BNF_LFP.construct_lfp)
        ((K false, false), T_specs) lthy;
    val T_sugars = map (the o BNF_FP_Def_Sugar.fp_sugar_of lthy) TNs;
  in
    (free, bound, frees_lives |> map (snd o dest_TFree), T_sugars, lthy)
  end;

val (add_prems, mk_prem_terms) =
  let
    fun test_TEqu (T1 : typ, T2 : typ) = if T1 = T2 then (T1, T2) else error "Types must be equal";

    fun mk_small_support t = t
      |> mk_supp
      |> mk_bound
      |> HOLogic.mk_Trueprop;
    val mk_small_support_imp = mk_small_support #> curry Logic.mk_implies;

    fun mk_bij t = t
      |> fastype_of
      |> dest_funT
      |> test_TEqu
      |> apply2 HOLogic.mk_UNIV
      |-> BNF_LFP_Util.mk_bij_betw t
      |> HOLogic.mk_Trueprop;
    val mk_bij_imp = mk_bij #> curry Logic.mk_implies;
  in
    (fold_rev (fn t => mk_bij_imp t o mk_small_support_imp t),
      maps (fn t => [mk_bij t, mk_small_support t]))
  end;

fun construct_binder_fp fp mrbnf_ks binding_relation lthy =
  let
    (* Error checking *)
    val co = if fp = Greatest_FP then true else if fp = Least_FP then false else
      error "Invalid fixpoint";
    val _ = if length mrbnf_ks > 0 then () else error "Need at least one mrbnf";
    val ((names, mrbnfs), ks) = split_list mrbnf_ks |>> split_list;

    (* Define raw datatype *)
    val (free, bound, sorts, T_sugars, lthy) =
      define_raw_terms co names mrbnfs ks binding_relation lthy;
    val n = length ks;
    val mutual = n > 1;
    val rec_live = foldr1 op+ ks;
    val k_ranges = let fun mk_range k = map (pair k) (1 upto k) in maps mk_range ks end;

    (* Normalise binding relation *)
    val binding_relation =
      let
        fun in_range i = 0 <= i andalso i <= rec_live - 1;
        fun remove_duplicates [] = []
          | remove_duplicates (x::xs) = case remove_duplicates xs of
            [] => [x]
            | (x'::xs) => if x = x' then x::xs else x::x'::xs;
      in
        map (remove_duplicates o sort int_ord o filter in_range) binding_relation
          |> filter (not o null)
      end;
    val fbound = length binding_relation;
    val passive = length sorts - fbound;
    val pfree = free - fbound;
    val pbound = bound - fbound;
    val plive = passive - pfree - pbound;
    val num_bindings = map length binding_relation |> foldr1 op+;

    val binding_matrix = map (fn b_rels => replicate rec_live false
      |> fold (fn i => nth_map i (K true)) b_rels) binding_relation;
    val binding_matrixt = transpose binding_matrix;
    val all_bindings = map (List.all I) binding_matrixt;
    val no_bindings = map (List.all not) binding_matrixt;
    fun map_binding_vector b_vec = @{map 3} (fn b => if b then K I else K) b_vec;
    fun map_binding_matrix xss yss = @{map 3} map_binding_vector binding_matrix xss yss;

    (* Helper functions *)
    fun subst_terms Ts terms =
      let
        fun subst_term Ts t = Term.subst_TVars ((Term.add_tvar_names t [] |> rev) ~~ Ts) t;
      in
        terms |> map (subst_term Ts)
      end;
    fun subst_typs Ts types =
      let
        fun subst_typ Ts T = Term.typ_subst_TVars ((Term.add_tvar_namesT T [] |> rev) ~~ Ts) T;
      in
        map (subst_typ Ts) types
      end;
    fun mk_inv_assms [] = []
      | mk_inv_assms (bij::supp::assms) = (@{thm bij_imp_bij_inv} OF [bij]) ::
        (@{thm supp_inv_bound} OF [bij, supp]) :: mk_inv_assms assms
      | mk_inv_assms _ = raise Match;
    val (id_prems, id_prems2, bij_id_prems, bij_prems, refl_prems) =
      let
        val ids = replicate fbound @{thms _} @ replicate pfree @{thms supp_id_bound} @
          replicate pbound @{thms bij_id supp_id_bound} @ replicate (2*fbound) @{thms _} |> flat;
        val bij_ids = replicate (2*fbound) @{thms _} @ replicate (pfree+pbound)
          @{thms bij_id supp_id_bound} @ replicate (2*fbound) @{thms _} |> flat;
        fun refls rs = replicate fbound @{thm _} @ replicate pfree (@{thm refl} RS rs) @
          replicate plive @{thm _} @ replicate pbound (@{thm refl} RS rs);
        fun OF_prems prems thm = thm OF prems;
        fun refl_prems n thm = OF_prems (replicate n @{thm _} @ refls thm);
      in
        (OF_prems ids, OF_prems (ids @ ids), OF_prems (ids @ bij_ids), OF_prems bij_ids, refl_prems)
      end;
    fun unfold_id lthy = unfold_thms lthy @{thms id_o o_id inv_id};

    (* Functions for sets and set_transfers *)
    val mk_rel_funD_settss = (fn sett => (rel_funD OF [sett OF (replicate fbound
      @{thm supp_id_bound})]) |> Drule.rotate_prems ~1) |> map o map;
    fun split_setss setss = map (chop fbound ##> drop passive ##>> chop fbound) setss
      |> split_list |>> split_list;
    fun split_setss_transp setss = transpose setss |> chop fbound ||> drop passive
      ||>> chop fbound;

    (* Make free types *)
    val (As, paramT) = lthy
      |> mk_TFrees' sorts
      ||> the_single o fst o mk_TFrees 1;
    val fAs = take fbound As;
    val CAs = subst_typs As (map #T T_sugars);
    val ctorsAs = maps (#ctrs o #ctr_sugar o #fp_ctr_sugar) T_sugars |> subst_terms As;
    val un_ctorsAs = if co
      then maps (the_single o #selss o #ctr_sugar o #fp_ctr_sugar) T_sugars |> subst_terms As
      else ctorsAs;
    fun mk_casexsAs T = map (#casex o #ctr_sugar o #fp_ctr_sugar) T_sugars |> subst_terms (As @ [T]);

    (* Make frees *)
    val (((((((((((ffs, fgs), xs), xs'), ys), ys'), zs), fsets), rho), param), varsOfs),
      frees_lthy) = lthy
      |> mk_Frees "f" (map2 (curry op -->) fAs fAs)
      ||>> mk_Frees "g" (map2 (curry op -->) fAs fAs)
      ||>> mk_Frees "x" (map (domain_type o fastype_of) ctorsAs)
      ||>> mk_Frees "x'" (map (domain_type o fastype_of) ctorsAs)
      ||>> mk_Frees "y" CAs
      ||>> mk_Frees "y'" CAs
      ||>> mk_Frees "z" fAs
      ||>> mk_Frees "A" (take fbound As |> map HOLogic.mk_setT)
      ||>> yield_singleton (mk_Frees "\<rho>") paramT
      ||>> yield_singleton (mk_Frees "Param") (HOLogic.mk_setT paramT)
      ||>> mk_Frees "varsOf" (take fbound As |> map (fn A => paramT --> HOLogic.mk_setT A));
    val ffs_ids = ffs @ map HOLogic.id_const (drop fbound As);
    val fids = map HOLogic.id_const fAs;

    (* Make mrbnf terms *)
    fun mk_rec_lives xs = map2 replicate ks xs |> flat;
    fun dest_rec_lives xs = unflat (map (fn k => replicate k []) ks) xs;
    fun mk_mrbnf_terms mk_Ts' As Bs CAs CBs of_mrbnf repl app_Us map_fun Ts =
      let
        val (Fs', TAs') = chop fbound As;
        val ((pFs', pTAs'), pBs') = chop pfree TAs' ||>> chop plive;
        val pTBs' = drop (fbound+pfree) Bs |> take plive;
        val CAs' = mk_rec_lives CAs;
        val CBs' = mk_rec_lives CBs;
        fun mk_mrbnf_id_map Fs Ts mrbnf = app_Us (pTBs' @ CBs' |> repl, of_mrbnf
          (deads_of_mrbnf mrbnf |> repl) (pTAs' @ CAs' |> repl)) (pBs' @ Fs' |> repl)
          (Fs' @ pFs' |> repl) mrbnf
          |> map_fun (Term.subst_atomic_types ((Fs' ~~ Fs) @ (mk_Ts' (TAs', pTBs') ~~ Ts)));
      in
        map (chop fbound Ts |-> mk_mrbnf_id_map) mrbnfs
      end;
    fun mk_mrbnf_id_terms of_mrbnf = mk_mrbnf_terms fst As As CAs CAs of_mrbnf;
    val mrbnf_maps_AsAs = mk_mrbnf_id_terms mk_map_of_mrbnf I op |> I As;
    val mrbnf_rels_AsAs = mk_mrbnf_id_terms mk_mr_rel_of_mrbnf I op |> I As;
    val mrbnf_setss_As = mk_mrbnf_id_terms mk_sets_of_mrbnf (2*fbound + passive + rec_live
      |> replicate) snd map As;
    val ((free_setss_Ast, bound_setss_Ast), _) = split_setss_transp mrbnf_setss_As;
    val ((_, bound_setss_As), rec_setss_As) = split_setss mrbnf_setss_As;
    fun comb_mrbnf_term non_recs recs mrbnf_term = list_comb (mrbnf_term,
      non_recs @ take fbound non_recs @ mk_rec_lives recs);

    (* Define rename primrec *)
    val ((renamesAs, _ (*renames*), _ (*rename_defs*), rename_simps), lthy) =
      let
        (* Make names and types *)
        val renameNs = map mk_renameN names;
        val rename_bs = map Binding.name renameNs;
        val renamesAs = map (fn CA => take fbound (map2 (curry op -->) As As) ---> (CA --> CA)) CAs;

        (* Make terms for primrec definition *)
        val recs = map2 (list_comb o rpair ffs o Free oo pair) renameNs renamesAs;
        fun mk_def_terms rename_t mrbnf_map_AsAs x ctorAs = (rename_t $ (ctorAs $ x), ctorAs $
          (comb_mrbnf_term ffs_ids (map HOLogic.id_const CAs) mrbnf_map_AsAs $
            (comb_mrbnf_term (map HOLogic.id_const As) recs mrbnf_map_AsAs $ x))) |> mk_Trueprop_eq
          |> fold_rev Logic.all (ffs @ [x]);
        fun mk_codef_terms rename_t mrbnf_map_AsAs y ctorAs un_ctorAs =
          (rename_t $ y, ctorAs $
            (comb_mrbnf_term (map HOLogic.id_const As) recs mrbnf_map_AsAs $ (comb_mrbnf_term
              ffs_ids (map HOLogic.id_const CAs) mrbnf_map_AsAs $ (un_ctorAs $ y))))
            |> mk_Trueprop_eq |> fold_rev Logic.all (ffs @ [y]);
        val def_terms = if co
          then @{map 5} mk_codef_terms recs mrbnf_maps_AsAs ys ctorsAs un_ctorsAs
          else @{map 4} mk_def_terms recs mrbnf_maps_AsAs xs ctorsAs;

        (* Define primrec and export terms and theorems *)
        val ((terms, defs, simpss), (new_lthy, old_lthy)) = lthy
          |> snd o Local_Theory.begin_nested
          |> (if co then primcorec else primrec) false
            (rename_bs ~~ renamesAs |> map (rpair NoSyn)) def_terms
          ||> `Local_Theory.end_nested;
        val phi = Proof_Context.export_morphism old_lthy new_lthy;
        val (termsAs, terms) = map_split (Morphism.term phi #> `dest_Const #>> fst) terms
          |>> map2 (Const oo rpair) renamesAs;
        val (defs, simps) = apply2 (Morphism.fact phi) (defs, flat simpss);
      in
        ((termsAs, terms, defs, simps), new_lthy)
      end;

    val ((mr_rel_refl_ids, mr_rel_refl_strong_ids, mr_rel_mono_strong_ids)) =
      let
        fun map_fun map of_mrbnf mrbnf =
          map (unfold_thms lthy [mr_rel_id_of_mrbnf mrbnf]) (of_mrbnf mrbnf);
        fun subs_rel of_mrbnf = map (map_fun I of_mrbnf) mrbnfs;
      in
        @{apply 3} subs_rel (rel_refl_of_mrbnf, rel_refl_strong_of_mrbnf, rel_mono_strong_of_mrbnf)
      end;
    val natLeq_bounds = map natLeq_bound_of_mrbnf mrbnfs;
    val Un_bounds = map Un_bound_of_mrbnf mrbnfs;
    val UNION_bounds = map UNION_bound_of_mrbnf mrbnfs;
    val set_boundss = map (fn mrbnf => set_bd_of_mrbnf mrbnf |> map
      (fn set_bd => @{thm ordLess_ordLeq_trans} OF [set_bd, var_large_of_mrbnf mrbnf])) mrbnfs;
    val var_infinites = map (unfold_thms lthy @{thms cinfinite_def Field_card_of}
      o UNIV_cinfinite_of_mrbnf) mrbnfs;
    val settss = map (map id_prems o mr_set_transfer_of_mrbnf) mrbnfs;
    val ((free_settss, bound_settss), rec_settss) = split_setss_transp (mk_rel_funD_settss settss);

    val supp_comp_bounds = map supp_comp_bound_of_mrbnf mrbnfs;
    val map_comps = map (unfold_id lthy o id_prems2 o map_comp_of_mrbnf) mrbnfs;
    val map_congs = map (unfold_id lthy o id_prems2 o map_cong_of_mrbnf) mrbnfs;
    val set_maps = map (map id_prems o set_map_of_mrbnf) mrbnfs;
    val set_map = flat set_maps;
    val mr_rel_monos = map (id_prems o mr_rel_mono_of_mrbnf) mrbnfs;
    val mr_rel_eqs = map mr_rel_eq_of_mrbnf mrbnfs;
    val mr_rel_maps = map (nth_map 2 (unfold_id lthy o bij_id_prems) o
      nth_map 1 (unfold_id lthy o id_prems2) o nth_map 0 (unfold_id lthy o id_prems2) o
      mr_rel_map_of_mrbnf) mrbnfs;
    val mr_rel_mono_strong0s = map (refl_prems (6*fbound+1) ballI o unfold_id lthy o id_prems2 o
      mr_rel_mono_strong0_of_mrbnf) mrbnfs;
    val mr_le_rel_OOs = map (unfold_id lthy o id_prems2 o mr_le_rel_OO_of_mrbnf) mrbnfs;
    val mr_rel_flips = map (unfold_id lthy o bij_prems o mr_rel_flip_of_mrbnf) mrbnfs;

    val prem_terms_ffs = mk_prem_terms ffs;
    val prem_terms_ffs_fgs = prem_terms_ffs @ mk_prem_terms fgs;
    val prem_terms_fsets = map (HOLogic.mk_Trueprop o mk_bound) fsets;
    fun prove lthy frees prems goal tac = Goal.prove_sorry lthy (map (fst o dest_Free) frees)
      prems goal (fn {context = ctxt, prems = assms} => tac ctxt assms)
      |> Thm.close_derivation \<^here>;
    fun prove_no_prems lthy frees goal tac = Goal.prove_sorry lthy (map (fst o dest_Free) frees) []
      goal (fn {context = ctxt, prems = _} => tac ctxt)
      |> Thm.close_derivation \<^here>;

    val mk_conjs = foldr1 HOLogic.mk_conj;
    val (split_conjs, split_Nconjs) =
      let
        fun split_conjs 1 thm = [thm]
          | split_conjs n thm = (conjunct1 OF [thm]) :: split_conjs (n-1) (conjunct2 OF [thm]);
      in (split_conjs n, (fn n => if n < 1 then single else split_conjs n)) end;

    fun mk_induct_inst lthy thm eqs ys = thm_instantiate_terms lthy
      (map2 (absfree o dest_Free) ys eqs @ ys |> map SOME) thm;
    fun mk_coinduct_inst frees_lthy Ts lthy thm eqs ys =
      let
        val (ls, rs) = frees_lthy
          |> mk_Frees "l" Ts
          ||> fst o mk_Frees "r" Ts;
        fun mk_rel l r y lhs rhs = HOLogic.mk_conj (HOLogic.mk_eq (l, lhs), HOLogic.mk_eq (r, rhs))
          |> list_exists_free [y] |> fold_rev (absfree o dest_Free) [l, r];
        val (lhss, rhss) = map_split HOLogic.dest_eq eqs;
        val rels = @{map 5} mk_rel ls rs ys lhss rhss;
        val insts = map2 (fn lhs => fn rhs => [lhs, rhs]) lhss rhss |> flat;
      in
        meta_mp OF [@{thm _} ,thm_instantiate_terms lthy (rels @ insts |> map SOME) thm]
      end;
    val raw_common_co_induct = hd T_sugars |> the o #fp_co_induct_sugar |> hd o #common_co_inducts
      |> (if co then unfold_thms lthy (map mr_rel_id_of_mrbnf mrbnfs) else I);
    fun mk_common_co_induct_inst frees_lthy Ts lthy = if co
      then mk_coinduct_inst frees_lthy Ts lthy raw_common_co_induct
      else mk_induct_inst lthy raw_common_co_induct;
    val raw_injects = maps (#injects o #ctr_sugar o #fp_ctr_sugar) T_sugars;
    val raw_splits = map (#split o #ctr_sugar o #fp_ctr_sugar) T_sugars;
    val raw_exhausts = map (#exhaust o #ctr_sugar o #fp_ctr_sugar) T_sugars;
    val raw_nchotomys = map (#nchotomy o #ctr_sugar o #fp_ctr_sugar) T_sugars;
    val raw_sels = if co
      then maps (the_single o #sel_thmss o #ctr_sugar o #fp_ctr_sugar) T_sugars
      else replicate n @{thm _};
    val raw_collapses = if co
      then maps (#collapses o #ctr_sugar o #fp_ctr_sugar) T_sugars
      else replicate n @{thm _};

    fun mk_rename_simp rename_t mrbnf_map_AsAs x y ctorAs un_ctorAs map_comp rename_simp raw_sel
      raw_collapse =
      let
        val recs = map (list_comb o rpair ffs) renamesAs;
        val rename_sel = if co
          then
            let
              val sel_goal = (un_ctorAs $ (list_comb (rename_t, ffs) $ y),
                (comb_mrbnf_term ffs_ids recs mrbnf_map_AsAs $ (un_ctorAs $ y))) |> mk_Trueprop_eq;
            in
              mk_rename_sel_tac map_comp rename_simp raw_sel
                |> prove lthy (ffs @ [y]) prem_terms_ffs sel_goal
                |> SOME
            end
          else NONE;
        val rename_sel' = case rename_sel of SOME thm => [thm] | _ => [];

        val goal = (list_comb (rename_t, ffs) $ (ctorAs $ x), ctorAs $
          (comb_mrbnf_term ffs_ids recs mrbnf_map_AsAs $ x)) |> mk_Trueprop_eq;
      in
        (rename_sel, mk_rename_simps_tac co map_comp rename_simp rename_sel' raw_sel raw_collapse
          |> prove lthy (ffs @ [x]) prem_terms_ffs goal)
      end;
    val (rename_sels, rename_simps) =
      @{map 10} mk_rename_simp renamesAs mrbnf_maps_AsAs xs ys ctorsAs un_ctorsAs map_comps
        rename_simps raw_sels raw_collapses |> split_list |>> map_filter I;

    val rename_ids =
      let
        fun mk_eq rename_t y = HOLogic.mk_eq (list_comb (rename_t, fids) $ y, y);
        val eqs = map2 mk_eq renamesAs ys;
        val common_co_induct_inst = mk_common_co_induct_inst frees_lthy CAs lthy eqs ys;
        val goal = mk_conjs eqs |> HOLogic.mk_Trueprop;

        fun mk_map_cong_thm mrbnf = trans OF [map_cong_of_mrbnf mrbnf, map_id0_of_mrbnf mrbnf
          RS fun_cong] RS @{thm trans[OF _ id_apply]};
        val map_cong_thms = map mk_map_cong_thm mrbnfs;
      in
        mk_rename_ids_tac co common_co_induct_inst rename_simps raw_injects map_cong_thms
          rename_sels (flat mr_rel_maps) mr_rel_refl_ids
          |> prove_no_prems lthy ys goal
          |> split_conjs
      end;
    val rename_id0s = map (fn thm => @{thm meta_eq_to_obj_eq} OF [
      Local_Defs.unfold0 lthy @{thms id_def[symmetric]} (Local_Defs.abs_def_rule lthy thm)
    ]) rename_ids

    val rename_comps =
      let
        fun mk_eq rename_t y = HOLogic.mk_eq
          (list_comb (rename_t, map2 (curry HOLogic.mk_comp) fgs ffs) $ y,
          list_comb (rename_t, fgs) $ (list_comb (rename_t, ffs) $ y));
        val eqs = map2 mk_eq renamesAs ys;
        val common_co_induct_inst = mk_common_co_induct_inst frees_lthy CAs lthy eqs ys;
        val goal = mk_conjs eqs |> HOLogic.mk_Trueprop;
      in
        mk_rename_comps_tac co common_co_induct_inst raw_injects rename_simps supp_comp_bounds
          map_comps map_congs rename_sels (flat mr_rel_maps) mr_rel_refl_ids
          |> prove lthy (ffs @ fgs @ ys) prem_terms_ffs_fgs goal
          |> split_conjs
          |> map (fn thm => thm RS sym)
      end;
    fun mk_rename_comp0s lthy = map2 (fn thm => fn rename_t =>
      let
        val goal = mk_Trueprop_eq (
          HOLogic.mk_comp (Term.list_comb (rename_t, fgs), Term.list_comb (rename_t, ffs)),
          Term.list_comb (rename_t, map2 (curry HOLogic.mk_comp) fgs ffs)
        );
        val comp_apply' = infer_instantiate' lthy [
          SOME (Thm.cterm_of lthy (Term.list_comb (rename_t, fgs))),
          SOME (Thm.cterm_of lthy (Term.list_comb (rename_t, ffs)))
        ] @{thm comp_apply[symmetric]}
       in prove lthy (ffs @ fgs) prem_terms_ffs_fgs goal (fn ctxt => fn prems =>
         let
          val thm' = @{thm meta_eq_to_obj_eq} OF [Local_Defs.abs_def_rule lthy (
            Local_Defs.unfold0 lthy [comp_apply'] (thm OF prems)
          )];
         in rtac ctxt thm' 1 end
       ) end
    );
    val rename_comp0s = mk_rename_comp0s lthy rename_comps renamesAs;

    fun mk_rename_bij lthy rename_t rename_comp0 rename_id0 =
      let val goal = HOLogic.mk_Trueprop (mk_bij (Term.list_comb (rename_t, ffs)));
      in prove lthy ffs prem_terms_ffs goal (mk_rename_bij_tac rename_comp0 rename_id0) end;
    val rename_bijs = @{map 3} (mk_rename_bij lthy) renamesAs rename_comp0s rename_id0s;

    fun mk_rename_inv_simp lthy rename_t rename_comp0 rename_id0 =
      let val goal = mk_Trueprop_eq (
        mk_inv (Term.list_comb (rename_t, ffs)),
        Term.list_comb (rename_t, map mk_inv ffs)
      ) in prove lthy ffs prem_terms_ffs goal (mk_rename_inv_simp_tac rename_comp0 rename_id0) end;
    val rename_inv_simps = @{map 3} (mk_rename_inv_simp lthy) renamesAs rename_comp0s rename_id0s;

    (* Define inductive predicate free *)
    fun mk_inductive i A z b_vec free_sets bound_sets lthy =
      let
        val i = if fbound > 1 then i else 0;
        val bs = map (Binding.name o mk_freeN i) names;
        val Ts = map (fn CA => A --> CA --> HOLogic.boolT) CAs;
        val inductive_flags = {quiet_mode = true, verbose = false, alt_name = Binding.empty,
          coind = false, no_elim = false, no_ind = false, skip_mono = false};
        val free_ts = map2 (Free oo pair o Binding.name_of) bs Ts;

        fun mk_terms ys x ctor free_t free_set bound_set rec_sets =
          let
            val concl = free_t $ z $ (ctor $ x);
            val t_free = [HOLogic.mk_mem (z, free_set $ x), concl];
            val add_non_mem = HOLogic.mk_mem (z, bound_set $ x) |> HOLogic.mk_not |> curry op ::;
            val concls = mk_rec_lives free_ts |> map2 (fn y => fn t => [t $ z $ y, concl]) ys
              |> swap o `(map add_non_mem) |-> map_binding_vector b_vec;
            val rec_ts = @{map 3} (fn t => t $ x |> rpair #> HOLogic.mk_mem #> curry op ::)
              rec_sets ys concls;
          in
            t_free :: rec_ts |> map (foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop)
          end;
        val terms = @{map 6} (mk_rec_lives ys |> mk_terms) xs ctorsAs free_ts free_sets
          bound_sets rec_setss_As |> flat;

        val (invar_result_raw, (new_lthy, lthy)) = lthy
          |> Local_Theory.begin_nested |> snd
          |> Inductive.add_inductive inductive_flags (map2 (rpair NoSyn oo pair) bs Ts) []
            (map (pair Binding.empty_atts) terms) []
          ||> `Local_Theory.end_nested;

        val phi = Proof_Context.export_morphism lthy new_lthy;
        val invar_result = Inductive.transform_result phi invar_result_raw;
        fun subst_free Ts free = Term.subst_TVars
          ((Term.add_tvar_namesT (fastype_of free |> range_type) [] |> rev) ~~ Ts) free;
        val frees_freesAs = map (`(subst_free As) o Morphism.term phi) free_ts |> split_list;
      in
        ((invar_result, frees_freesAs), new_lthy)
      end;
    val ((frees_invar_results, (freessAs, _ (*freess*))), lthy) =
      @{fold_map 6} mk_inductive (1 upto fbound) (take fbound As) zs binding_matrix
        free_setss_Ast bound_setss_Ast lthy |>> apsnd split_list o split_list;

    (* Define FVars *)
    fun define_FVars i z frees lthy =
      let
        val i = if fbound > 1 then i else 0;
        val (s, T) = dest_Free z;
        fun mk_rhs y free = HOLogic.mk_Collect (s, T, free $ z $ y) |> (absfree o dest_Free) y;
      in
        @{fold_map 2} new_definition (map (Binding.name o mk_FVarsN i) names)
          (map2 mk_rhs ys frees) lthy
      end;
    val ((FVars_termss, FVars_defss), lthy) = @{fold_map 3} define_FVars (1 upto fbound) zs freessAs
      lthy |>> split_list o map (split_list o map (fn x => (#2 x, #3 x)));
    val FVarsssAs = map (subst_terms As) FVars_termss;

    fun mk_free_FVars z y freeAs FVarsAs FVars_def =
      (fn ctxt => unfold_tac ctxt [FVars_def, mem_Collect_eq]) |> prove_no_prems lthy [z, y]
        (mk_Trueprop_eq (freeAs $ z $ y, HOLogic.mk_mem (z, FVarsAs $ y)));
    val free_FVarsss = @{map 4} (fn z => @{map 4} (mk_free_FVars z) ys) zs freessAs FVarsssAs
      FVars_defss;

    val (FVars_inducts, (_, FVars_intross, FVars_elimss)) = @{apply 3}
      (flat free_FVarsss |> unfold_thms lthy |> map |> map)
      ([map #induct frees_invar_results], map #intrs frees_invar_results,
        map #elims frees_invar_results) |> `(the_single o #1);

    fun mk_FVars_ctor FVars_ts b_vec FVars_intros x ctor FVars_t rec_sets free_set bound_set
      FVars_elim =
      let
        fun add_Diff t = mk_minus t (bound_set $ x);
        fun mk_UN set (y, t) = t $ y |> (absfree o dest_Free) y |> mk_UNION (set $ x);
        val UNs = ys ~~ FVars_ts |> mk_rec_lives |> map2 mk_UN rec_sets
          |> swap o `(map add_Diff) |-> map_binding_vector b_vec;
        val goal = (FVars_t $ (ctor $ x), foldl1 mk_union (free_set $ x :: UNs)) |> mk_Trueprop_eq;
      in
        mk_FVars_ctorss_Tac raw_injects FVars_intros FVars_elim
          |> prove_no_prems lthy [x] goal
      end;
    val FVars_ctorss = @{map 6} (fn FVars_ts => fn b_rels => fn FVars_intros => @{map 7}
        (mk_FVars_ctor FVars_ts b_rels FVars_intros) xs ctorsAs FVars_ts rec_setss_As)
      FVarsssAs binding_matrix FVars_intross free_setss_Ast bound_setss_Ast FVars_elimss;

    fun mk_FVars_rename_les z f FVars_ts FVars_induct FVars_intros =
      let
        val prems = map2 (HOLogic.mk_mem o pair z o op $ oo pair) FVars_ts ys;
        val concls = @{map 3} (HOLogic.mk_mem o pair (f $ z) o op $ oo rpair o op $ oo pair o
          list_comb o rpair ffs) renamesAs ys FVars_ts;
        val goal = map2 (curry HOLogic.mk_imp) prems concls |> mk_conjs |> HOLogic.mk_Trueprop;
      in
        mk_FVars_rename_les_tac mutual FVars_induct FVars_intros rename_simps set_map
          |> prove lthy (ffs @ ys @ [z]) prem_terms_ffs goal
          |> split_conjs
      end;
    val FVars_rename_less = @{map 5} mk_FVars_rename_les zs ffs FVarsssAs FVars_inducts
      FVars_intross;

    fun mk_FVars_rename f y rename_recAs rename_comp rename_id FVars_t FVars_rename_le =
      let
        val goal = (FVars_t $ (list_comb(rename_recAs, ffs) $ y), mk_image f $ (FVars_t $ y))
          |> mk_Trueprop_eq;
        fun mk_FVars_rename_le_alt assms = FVars_rename_le RS mp OF mk_inv_assms assms;
      in
        mk_FVars_rename_tac rename_comp rename_id FVars_rename_le mk_FVars_rename_le_alt
          |> prove lthy (ffs @ [y]) prem_terms_ffs goal
      end;
    val FVars_renamess = @{map 3}
      (fn f => @{map 6} (mk_FVars_rename f) ys renamesAs rename_comps rename_ids)
      ffs FVarsssAs FVars_rename_less;

    fun mk_card_of_FVars_bounds rec_set_boundss free_set_bounds free_sets i A z FVarssAs
      FVars_induct lthy = if co
      then let
          val tT = BNF_FP_Util.mk_sumTN_balanced CAs;
          val (nat, t) = frees_lthy
            |> yield_singleton (mk_Frees "n") HOLogic.natT
            ||> fst o yield_singleton (mk_Frees "t") tT;

          val (set_levelAs, _ (*set_level_def*), set_level_simps, lthy) =
            let
              (* Make names and types *)
              val i = if fbound > 1 then i else 0;
              val set_levelN = mk_set_levelN i names;
              val set_level_b = Binding.name set_levelN;
              val set_levelAs = HOLogic.natT --> tT --> HOLogic.mk_setT A;

              (* Make terms for primrec definition *)
              val set_level_t = Free (set_levelN, set_levelAs);
              val zero_term = (set_level_t $ HOLogic.zero $ t, Const (@{const_name bot},
                HOLogic.mk_setT A)) |> mk_Trueprop_eq |> Logic.all t;

              val casexs = mk_casexsAs (HOLogic.mk_setT A);
              fun mk_union_term x (y, i) set = mk_UNION (set $ x)
                (set_level_t $ nat $ mk_sumN_balanced ys i |> absfree (dest_Free y));
              fun mk_case_term x y casex fset sets = casex $ (fset $ x ::
                  map2 (mk_union_term x) (ys ~~ (1 upto n) |> mk_rec_lives) sets |> foldl1 mk_union
                |> absfree (dest_Free x)) $ y |> absfree (dest_Free y);
              val suc_term = mk_Trueprop_eq (set_level_t $ HOLogic.mk_Suc nat $ t,
                (@{map 5} mk_case_term xs ys casexs free_sets rec_setss_As
                  |> mk_case_sumN_balanced) $ t) |> fold_rev Logic.all [nat, t];

              (* Define primrec and export terms and theorems *)
              val ((terms, defs, simpss), (new_lthy, old_lthy)) = lthy
                |> snd o Local_Theory.begin_nested
                |> primrec false [((set_level_b, set_levelAs), NoSyn)] [zero_term, suc_term]
                ||> `Local_Theory.end_nested;
              val phi = Proof_Context.export_morphism old_lthy new_lthy;
              val termAs = the_single terms |> Morphism.term phi |> dest_Const |> fst
                |> (Const oo rpair) set_levelAs;
              val (def, simps) = apply2 (Morphism.fact phi) (defs, flat simpss) |>> the_single;
            in
              (termAs, def, simps, new_lthy)
            end;

          val set_level_bound =
            let
              val goal = set_levelAs $ nat $ t |> mk_bound;
              val nat_induct = thm_instantiate_terms lthy [list_all_free [t] goal
                |> absfree (dest_Free nat) |> SOME] @{thm nat.induct} RS spec;
            in
              mk_set_level_bound_tac nat_induct set_level_simps raw_splits Un_bounds UNION_bounds
                free_set_bounds (flat rec_set_boundss)
                |> prove_no_prems lthy [nat, t] (HOLogic.mk_Trueprop goal)
            end;

          val FVars_overapproxs =
            let
              fun mk_eq FVars_t y i = HOLogic.mk_imp (HOLogic.mk_mem (z, FVars_t $ y),
                HOLogic.mk_mem (z, mk_UNION (HOLogic.mk_UNIV HOLogic.natT)
                  (set_levelAs $ nat $ mk_sumN_balanced ys i |> absfree (dest_Free nat))));
              val goal = @{map 3} mk_eq FVarssAs ys (1 upto n) |> mk_conjs |> HOLogic.mk_Trueprop;
            in
              mk_FVars_overapprox_tac mutual FVars_induct set_level_simps raw_injects raw_splits
                |> prove_no_prems lthy (ys @ [z]) goal
                |> split_conjs
                |> map (fn thm => thm RS mp)
            end;

          fun mk_card_of_FVars_bound FVars_t y FVars_overapprox UNION_bound natLeq_bound =
            let
              val goal = FVars_t $ y |> mk_bound |> HOLogic.mk_Trueprop;
              val UNION_bound = thm_instantiate_terms lthy [SOME @{term "UNIV::nat set"}]
                UNION_bound OF [@{thm _}, set_level_bound];
            in
              mk_co_card_of_FVars_bounds_tac FVars_overapprox UNION_bound natLeq_bound
                |> prove_no_prems lthy [y] goal
            end;
        in
          @{map 5} mk_card_of_FVars_bound FVarssAs ys FVars_overapproxs UNION_bounds natLeq_bounds
            |> rpair lthy
        end
      else let
          val eqs = map2 (mk_bound o op $ oo pair) FVarssAs ys;
          val common_co_induct_inst = mk_common_co_induct_inst frees_lthy CAs lthy eqs ys;
          val goal = mk_conjs eqs |> HOLogic.mk_Trueprop;
          val intross = [Un_bounds, UNION_bounds, free_set_bounds] @ rec_set_boundss
            |> transpose;
        in
          mk_card_of_FVars_bounds_tac common_co_induct_inst (flat FVars_ctorss) intross
            |> prove_no_prems lthy ys goal
            |> split_conjs
            |> rpair lthy
        end;
    val (card_of_FVars_boundss, lthy) =
      let
        val (free_sboundss, rec_sboundss) = split_setss_transp set_boundss |>> fst;
      in
        @{fold_map 7} (mk_card_of_FVars_bounds rec_sboundss) free_sboundss free_setss_Ast
          (1 upto fbound) (take fbound As) zs FVarsssAs FVars_inducts lthy
      end;

    (* Define alpha relation *)
    val (alphas_invar_result, (alphasAs, _ (*alphas*)), FVarsBssAs, lthy) =
      let
        val bs = map (Binding.name o mk_alphaN) names;
        val Ts = map (fn CA => CA --> CA --> HOLogic.boolT) CAs;
        val inductive_flags = {quiet_mode = true, verbose = false, alt_name = Binding.empty,
          coind = true, no_elim = false, no_ind = false, skip_mono = false};
        val alpha_ts = map2 (Free oo pair o Binding.name_of) bs Ts;

        fun mk_term x x' ctor alpha_t bound_sets rec_sets mrbnf_rel_AsAs =
          let
            val FVarsBs =
              let
                fun mk_zips FVars_ts = map (op $ o rpair x) rec_sets ~~ mk_rec_lives FVars_ts;
                fun mk_bound_minus bound_set t = mk_minus t (bound_set $ x);
                fun mk_UNION_term bound_set FVars_ts b_rels = map (nth (mk_zips FVars_ts)
                  #-> mk_UNION) b_rels |> map (mk_bound_minus bound_set)
                  |> foldl1 mk_union;
              in
                @{map 3} mk_UNION_term bound_sets FVarsssAs binding_relation
              end;
            val prems1 = map2 mk_id_on FVarsBs ffs;

            val recs_consts = ys ~~ ys' ~~ renamesAs ~~ alpha_ts |> mk_rec_lives;
            val rename_args = apply2 (replicate rec_live |> map) (fids, ffs)
              |-> transpose oo map_binding_matrix
              |> map2 (fn b => if b then K NONE else SOME) no_bindings;
            fun mk_rec_rel (_, alpha_t) NONE = alpha_t
              | mk_rec_rel (((y, y'), rename_t), alpha_t) (SOME fs) = alpha_t $ (list_comb
                (rename_t, fs) $ y) $ y' |> fold_rev (absfree o dest_Free) [y, y'];
            val ideqs = map2 I (replicate free HOLogic.id_const @ replicate plive HOLogic.eq_const @
              replicate pbound HOLogic.id_const) As;
            val prem0 = list_comb (mrbnf_rel_AsAs, ideqs @ ffs @
              map2 mk_rec_rel recs_consts rename_args) $ x $ x';
            val concl = alpha_t $ (ctor $ x) $ (ctor $ x');
          in
            foldr1 Logic.mk_implies (prems1 @ [prem0, concl] |> map HOLogic.mk_Trueprop)
              |> add_prems ffs |> rpair FVarsBs
          end;
        val (terms, FVarsBss) = @{map 7} mk_term xs xs' ctorsAs alpha_ts bound_setss_As
          rec_setss_As mrbnf_rels_AsAs |> split_list;

        val monos = map (fn mr_rel_mono => mr_rel_mono OF replicate fbound
          @{thm supp_id_bound}) mr_rel_monos @ @{thms conj_context_mono};

        val (invar_result_raw, (new_lthy, lthy)) = lthy
          |> Local_Theory.begin_nested |> snd
          |> Inductive.add_inductive inductive_flags (map2 (rpair NoSyn oo pair) bs Ts) []
            (map (pair Binding.empty_atts) terms) monos
          ||> `Local_Theory.end_nested;

        val phi = Proof_Context.export_morphism lthy new_lthy;
        val invar_result = Inductive.transform_result phi invar_result_raw;
        val frees_freesAs = map (Morphism.term phi) alpha_ts |> `(subst_terms As);
      in
        (invar_result, frees_freesAs, FVarsBss, new_lthy)
      end;

    val alpha_coinduct = #induct alphas_invar_result;
    val alpha_intros = #intrs alphas_invar_result;
    val alpha_elims = #elims alphas_invar_result;
    val T_cases = map (the o Induct.lookup_casesT lthy o fst o dest_Type) CAs;
    val alpha_intros_id = map (fn thm => thm OF (replicate fbound @{thms bij_id supp_id_bound}
      |> flat)) alpha_intros;

    val alpha_refls =
      let
        fun mk_eq y y' alpha_t = HOLogic.mk_imp (HOLogic.mk_eq (y, y'), alpha_t $ y $ y')
          |> list_all_free [y, y'];
        val eqs = @{map 3} mk_eq ys ys' alphasAs;
        val goal = mk_conjs eqs |> HOLogic.mk_Trueprop;

        fun mk_case thm ct = infer_instantiate' lthy [SOME ct] thm;
        val mk_cases = map mk_case T_cases;
      in
        mk_alpha_refls_tac mutual alpha_coinduct mk_cases raw_injects rename_ids
          mr_rel_refl_strong_ids alpha_intros
          |> prove_no_prems lthy (ys @ ys') goal
          |> split_conjs
          |> map (fn thm => thm RS @{thm spec2} RS mp OF [refl])
      end;

    val alpha_bijs =
      let
        val ((fs', ls), rs) = frees_lthy
          |> mk_Frees "f'" (map2 (curry op -->) As As |> take fbound)
          ||>> mk_Frees "l" CAs
          ||> fst o mk_Frees "r" CAs;

        fun mk_eq l r y y' alpha_t rename_t FVars_ts =
          let
            fun mk_rename_eq fs y lhs = HOLogic.mk_eq (lhs, list_comb (rename_t, fs) $ y);
            val rename_eqs = [alpha_t $ y $ y', mk_rename_eq ffs y l, mk_rename_eq fs' y' r];

            fun mk_ball_eq FVars_t f f' z = HOLogic.mk_eq (f $ z, f' $ z) |> absfree (dest_Free z)
              |> mk_Ball (FVars_t $ y);
            val ball_eqs = @{map 4} mk_ball_eq FVars_ts ffs fs' zs;

            val prem_terms = map HOLogic.dest_Trueprop (prem_terms_ffs @ mk_prem_terms fs');
            val prem = rename_eqs @ ball_eqs @ prem_terms |> mk_conjs
              |> list_exists_free ([y, y'] @ ffs @ fs');
            val concl = alpha_t $ l $ r;
          in
            HOLogic.mk_imp (prem, concl) |> list_all_free [l, r]
          end;
        val eqs = @{map 7} mk_eq ls rs ys ys' alphasAs renamesAs (transpose FVarsssAs);
        val goal = mk_conjs eqs |> HOLogic.mk_Trueprop;

        fun mk_exIss rename_comps fs fs' =
          let
            val exI_ts1 = apply2 (replicate rec_live |> map) (fs, fs')
              |-> transpose oo map_binding_matrix;
            val exI_ts2 = replicate rec_live fs';
            val exI_ts = exI_ts1 ~~ exI_ts2;
            val map_fun = (fn t => infer_instantiate' lthy [NONE, SOME t] exI) |> map |> apply2;
          in
            mk_rec_lives rename_comps ~~ map map_fun exI_ts
          end;

        fun after_qed thm =
          let
            fun OF_exI thm = thm OF @{thms exI};
            fun OF_conj_rotated thm = thm OF @{thms conjI[rotated]};
            fun OF_conjI_folded n thm = if n <= 0 then thm else thm OF [mk_conjIN n];
          in
            ((thm RS @{thm spec2} RS mp)
                |> funpow (2*(fbound+1)) OF_exI
                OF @{thms conjI[rotated]}
                OF @{thms conjI[OF refl]}
                OF @{thms conjI[OF refl]})
              |> funpow fbound OF_conj_rotated
              |> OF_conjI_folded (4*fbound)
          end;
      in
        mk_alpha_bij_tac mutual fbound num_bindings alpha_coinduct alpha_elims rename_simps
          (flat FVars_renamess) rename_comps raw_injects mk_exIss (flat FVars_ctorss)
          supp_comp_bounds mr_rel_maps set_maps mr_rel_mono_strong0s
          |> prove_no_prems lthy (ys @ ys') goal
          |> split_conjs
          |> map after_qed
      end;

    fun mk_alpha_bij_eq alpha_t rename_t y y' alpha_bij rename_comp rename_id =
      let
        val rename_t_ffs = list_comb (rename_t, ffs);
        val goal = (alpha_t $ (rename_t_ffs $ y) $ (rename_t_ffs $ y'), alpha_t $ y $ y')
          |> mk_Trueprop_eq;
        fun mk_alpha_bij_alt assms = (alpha_bij OF (assms @ assms)) |> Drule.rotate_prems ~1;
        fun mk_alpha_bij_alts assms = apply2 mk_alpha_bij_alt (mk_inv_assms assms, assms);
      in
        mk_alpha_bij_eq_tac rename_comp rename_id mk_alpha_bij_alts
          |> prove lthy (ffs @ [y, y']) prem_terms_ffs goal
      end;
    val alpha_bij_eqs = @{map 7} mk_alpha_bij_eq alphasAs renamesAs ys ys' alpha_bijs rename_comps
      rename_ids;

    fun mk_alpha_bij_eq_inv alpha_t rename_t y y' rename_comp rename_id alpha_bij_eq =
      let
        val goal = mk_Trueprop_eq (alpha_t $ (list_comb (rename_t, ffs) $ y) $ y',
          alpha_t $ y $ (list_comb (rename_t, map mk_inv ffs) $ y'));
        fun mk_unfolds [] = [rename_id]
          | mk_unfolds (bij::assms) = (@{thm inv_o_simp2} OF [bij]) :: mk_unfolds (drop 1 assms);
        val t_insts = map mk_inv ffs @ ffs @ [y'] |> map SOME;
        fun mk_rename_comp_alt assms = thm_instantiate_terms lthy t_insts rename_comp
          |> unfold_thms lthy (mk_unfolds assms) RS sym;
      in
        mk_alpha_bij_eq_inv_tac mk_rename_comp_alt alpha_bij_eq
          |> prove lthy (ffs @ [y, y']) prem_terms_ffs goal
      end;
    val alpha_bij_eq_invs = @{map 7} mk_alpha_bij_eq_inv alphasAs renamesAs ys ys' rename_comps
      rename_ids alpha_bij_eqs;

    fun mk_alpha_FVars_les reverse z FVars_ts FVars_induct set_transfers =
      let
        fun mk_eq y y' alpha_t FVars_t = HOLogic.mk_imp (HOLogic.mk_mem (z, FVars_t $ y),
          HOLogic.mk_imp (list_comb (alpha_t, if reverse then [y', y] else [y, y']),
            HOLogic.mk_mem (z, FVars_t $ y')) |> list_all_free [y']);
        val eqs = @{map 4} mk_eq ys ys' alphasAs FVars_ts;
        val goal = mk_conjs eqs |> HOLogic.mk_Trueprop;
      in
        mk_alpha_FVars_les_tac mutual reverse (rec_live+1) (mk_rec_lives alpha_bij_eq_invs)
          FVars_induct alpha_elims raw_injects (flat FVars_renamess) (flat FVars_ctorss)
          set_transfers
          |> prove_no_prems lthy (ys @ [z]) goal
          |> split_conjs
          |> map (fn thm => thm RS mp RS spec RS mp)
      end;
    val alpha_FVars_less =
      let
        fun zip_opt (xs, NONE) = map (rpair NONE) xs
          | zip_opt (xs, SOME ys) = xs ~~ map SOME ys;
        fun add_bound_sett rec_settss free_setts bound_setts b_vec =
          map (rpair NONE) rec_settss |> swap o `(SOME bound_setts |> map o apsnd o K)
            |-> map_binding_vector b_vec |> map zip_opt
            |> (map2 (curry op:: o rpair NONE) free_setts) o transpose;
        val set_transferss = @{map 3} (add_bound_sett rec_settss) free_settss bound_settss
          binding_matrix;
      in
        apply2 (fn reverse => @{map 4} (mk_alpha_FVars_les reverse) zs FVarsssAs
          FVars_inducts set_transferss) (false, true) |-> map2 (curry op ~~)
      end;

    fun mk_alpha_FVars y y' alpha_t FVars_t (alpha_FVars_le_left, alpha_FVars_le_right) =
      let
        val goal = Logic.mk_implies (alpha_t $ y $ y' |> HOLogic.mk_Trueprop,
          mk_Trueprop_eq (FVars_t $ y, FVars_t $ y'));
      in
        mk_alpha_FVars_tac alpha_FVars_le_left alpha_FVars_le_right
          |> prove_no_prems lthy [y, y'] goal
      end;
    val alpha_FVarsss = map2 (@{map 5} mk_alpha_FVars ys ys' alphasAs) FVarsssAs alpha_FVars_less;

    val alpha_syms =
      let
        fun mk_eq y y' alpha_t = HOLogic.mk_imp (alpha_t $ y' $ y, alpha_t $ y $ y')
          |> list_all_free [y, y'];
        val eqs = @{map 3} mk_eq ys ys' alphasAs;
        val goal = mk_conjs eqs |> HOLogic.mk_Trueprop;

        fun mk_b_setts rec_setts = (nth rec_setts |> map o map) binding_relation;
        val settsss = map op~~ (transpose bound_settss ~~ (transpose rec_settss |> map mk_b_setts));
      in
        mk_alpha_sym_tac mutual fbound alpha_coinduct alpha_elims (flat FVars_renamess)
          alpha_FVarsss alpha_bij_eq_invs mr_rel_flips mr_rel_mono_strong0s settsss
          |> prove_no_prems lthy (ys @ ys') goal
          |> split_conjs
          |> map (fn thm => thm RS spec RS spec RS mp)
      end;

    val alpha_transs =
      let
        val ss = mk_Frees "s" CAs frees_lthy |> fst;
        fun mk_eq y y' s alpha_t = (HOLogic.mk_conj (alpha_t $ y $ s, alpha_t $ s $ y')
          |> list_exists_free [s], alpha_t $ y $ y') |> HOLogic.mk_imp |> list_all_free [y, y'];
        val eqs = @{map 4} mk_eq ys ys' ss alphasAs;
        val goal = mk_conjs eqs |> HOLogic.mk_Trueprop;

        val supp_comp_bounds = map supp_comp_bound_of_mrbnf mrbnfs;
        fun mk_b_setts rec_setts = (nth rec_setts |> map o map) binding_relation;
        val settsss = map op~~ (transpose bound_settss ~~ (transpose rec_settss |> map mk_b_setts));

        val supp_ids = replicate fbound @{thm supp_id_bound};
        fun mk_mr_rel_mono_alt mr_rel_mono mr_le_rel_OO = unfold_thms lthy @{thms id_o}
          (Drule.rotate_prems ~1 (mr_rel_mono RS @{thm predicate2D}) OF [mr_le_rel_OO RS
            @{thm predicate2D}] OF (supp_ids @ replicate (2*fbound) @{thm _} @ supp_ids))
          |> Drule.rotate_prems (4*fbound) OF @{thms relcomppI};
        val mr_rel_mono_alts = map2 mk_mr_rel_mono_alt
          (map (id_prems o mr_rel_mono_of_mrbnf) mrbnfs)
          (map (unfold_id lthy o id_prems2 o mr_le_rel_OO_of_mrbnf) mrbnfs);

        fun is_unique [] = []
          | is_unique (x::xs) = (exists (curry op = x) xs, x) :: is_unique xs;
        fun is_unique_grouped [] xs = is_unique xs
          | is_unique_grouped (k::ks) xs = chop k xs |>> is_unique ||> is_unique_grouped ks |> op @;
        fun filter_unique xs = filter_like (is_unique_grouped ks (transpose binding_matrix)
          |> map fst |> filter_like no_bindings not) not xs;

        fun mk_alpha_bij alpha_bij = Drule.rotate_prems ~1 alpha_bij;
        fun mk_rename_comp (rename_comp, prems) = unfold_thms lthy @{thms id_o} (rename_comp RS sym
          OF (replicate fbound prems |> flat));
        val (alpha_bijs, rename_comps) = mk_rec_lives alpha_bijs ~~ (mk_rec_lives rename_comps ~~
          (apply2 (replicate fbound o replicate rec_live) (@{thms bij_id supp_id_bound},
              @{thms _ _}) |-> map flat o transpose oo map_binding_matrix))
          |> filter_like no_bindings not |> split_list
          ||> map mk_rename_comp o filter_unique |>> map mk_alpha_bij;
      in
        mk_alpha_trans_tac mutual fbound supp_comp_bounds alpha_coinduct alpha_elims raw_injects
          rename_comps alpha_bijs mr_rel_mono_alts (flat FVars_renamess) alpha_FVarsss settsss
          |> prove_no_prems lthy (ys @ ys') goal
          |> split_conjs
          |> map (fn thm => thm RS spec RS spec RS mp OF [exI] OF [conjI])
      end;

    val card_of_FVarsB_boundss =
      let
        fun mk_b_bounds set_bounds b_rels card_of_FVars_bounds =
          (set_bounds ~~ mk_rec_lives card_of_FVars_bounds |> map o nth) b_rels |> split_list;
        fun mk_UNION_bound UNION_bound set_bound card_of_FVars_bound = @{thm ordLeq_ordLess_trans}
          OF [@{thm card_of_diff}, UNION_bound OF [set_bound, card_of_FVars_bound]];
        fun Un_bound_OF Un_bound = foldl1 (fn (thm1, thm2) => Un_bound OF [thm1, thm2]);
        fun mk_card_of_FVarsB_bound Un_bound UNION_bound b_rel_bounds set_bounds = b_rel_bounds
          |-> mk_b_bounds set_bounds |-> map2 (mk_UNION_bound UNION_bound) |> Un_bound_OF Un_bound;
        fun mk_card_of_FVarsB_bounds Un_bound UNION_bound = map2 (mk_card_of_FVarsB_bound Un_bound
          UNION_bound) (binding_relation ~~ card_of_FVars_boundss);
        val rec_set_boundsss = map (replicate fbound o take rec_live o drop (2*fbound+passive))
          set_boundss;
      in
        @{map 3} mk_card_of_FVarsB_bounds Un_bounds UNION_bounds rec_set_boundsss
      end;

    fun refresh_set FVarsBs x mrbnf_map_AsAs bound_sets mrbnf_set_bounds mrbnf_var_infinite Un_bound
      card_of_FVarsB_bounds set_map =
      let
        val recs_consts = renamesAs ~~ map HOLogic.id_const CAs |> mk_rec_lives;
        val rename_args = apply2 (replicate rec_live |> map) (fids, ffs)
          |-> transpose oo map_binding_matrix
          |> map2 (fn b => if b then K NONE else SOME) no_bindings;
        fun mk_rec_rel (_, id) NONE = id
          | mk_rec_rel (rename_t, _) (SOME fs) = list_comb (rename_t, fs);
        val map_t = list_comb (mrbnf_map_AsAs, map HOLogic.id_const As @ ffs @
          map2 mk_rec_rel recs_consts rename_args) $ x;

        fun mk_int_empty set_t fset = HOLogic.mk_eq (mk_inter (set_t $ map_t, fset),
          Const (@{const_name bot}, fastype_of fset));

        val concls1 = map2 mk_id_on FVarsBs ffs;
        val concls2 = map2 mk_int_empty bound_sets fsets;
        val goal = map HOLogic.dest_Trueprop prem_terms_ffs @ concls1 @ concls2 |> mk_conjs
          |> list_exists_free ffs |> HOLogic.mk_Trueprop;

        fun mk_insert_thms terms = thm_instantiate_terms lthy (map SOME terms)
          @{thm card_of_ordLeq[THEN iffD2, OF ordLess_imp_ordLeq, of "set \<inter> fset"
            "UNIV - (set \<union> FVarsB \<union> fset)" for set fset FVarsB]};
        val insert_thms = map mk_insert_thms
          (transpose [map (fn thm => thm $ x) bound_sets, fsets, FVarsBs]);
        fun mk_exI_thms terms = thm_instantiate_terms lthy (NONE :: map SOME terms)
          @{thm exI[of _ "extU (set \<inter> fset) (u ` (set \<inter> fset)) u" for set fset u]};
        val exI_thms = map mk_exI_thms (transpose [map (fn thm => thm $ x) bound_sets, fsets]);
        fun mk_extU_thms terms = thm_instantiate_terms lthy (NONE :: map SOME terms)
          @{thm extU[of u "set \<inter> fset" "u ` (set \<inter> fset)" for set fset u]};
        val extU_thms = map mk_extU_thms (transpose [map (fn thm => thm $ x) bound_sets, fsets]);
      in
        mk_refresh_set_tac fbound mrbnf_var_infinite Un_bound insert_thms mrbnf_set_bounds
          card_of_FVarsB_bounds exI_thms extU_thms set_map
          |> prove lthy (fsets @ [x]) prem_terms_fsets goal
      end;
    val refresh_sets =
      let
        fun take_bounds xss = map (take fbound o drop (fbound+passive)) xss;
      in
        @{map 9} refresh_set FVarsBssAs xs mrbnf_maps_AsAs bound_setss_As (take_bounds set_boundss)
          var_infinites Un_bounds card_of_FVarsB_boundss set_maps
      end;

    fun mk_avoid_term x x' alpha_t ctor bound_sets =
      let
        fun mk_eq set_t fset = HOLogic.mk_eq (mk_inter (set_t $ x', fset),
          Const (@{const_name bot}, fastype_of fset));
      in
        map2 mk_eq bound_sets fsets @ [alpha_t $ (ctor $ x) $ (ctor $ x')] |> mk_conjs
      end;

    fun mk_refresh bound_sets x x' alpha_t ctor refresh_set mrbnf_map_AsAs alpha_intro rel_map
      rel_refl_id =
      let
        val goal = mk_avoid_term x x' alpha_t ctor bound_sets |> list_exists_free [x']
          |> HOLogic.mk_Trueprop;

        fun mk_exI cfs =
          let
            fun mk_rename_t b rename_t CA fs = if b then HOLogic.id_const CA else
              list_comb (rename_t, fs);
            val fs = map Thm.term_of cfs;
            val ids = map (HOLogic.id_const o domain_type o fastype_of) fs;
            val rename_args = apply2 (replicate rec_live |> map) (ids, fs)
              |-> transpose oo map_binding_matrix
              |> @{map 4} mk_rename_t no_bindings (mk_rec_lives renamesAs) (mk_rec_lives CAs);
            val t = list_comb (mrbnf_map_AsAs, map HOLogic.id_const As @ fs @ rename_args) $ x;
          in
            thm_instantiate_terms lthy [NONE, SOME t] @{thm exI}
          end;
        fun mk_refresh_set assms = thm_instantiate_terms lthy [SOME x] (refresh_set OF assms);
      in
        mk_refresh_tac alpha_intro alpha_refls rel_map rel_refl_id mk_refresh_set mk_exI
          |> prove lthy (x :: fsets) prem_terms_fsets goal
      end;
    val refreshs = @{map 10} mk_refresh bound_setss_As xs xs' alphasAs ctorsAs refresh_sets
      mrbnf_maps_AsAs alpha_intros mr_rel_maps mr_rel_refl_ids;

    (* Define avoid *)
    val ((avoid_terms, avoid_defs), lthy) =
      let
        fun mk_rhs x x' alpha_t ctor bound_sets =
          let
            val (x'T, x'Free) = dest_Free x' |> `snd;
          in
            mk_avoid_term x x' alpha_t ctor bound_sets |> absfree x'Free |>
              (fn t => HOLogic.choice_const x'T $ t) |> fold_rev (absfree o dest_Free) (x :: fsets)
          end;
      in
        @{fold_map 2} new_definition (map (Binding.name o mk_avoidN) names)
          (@{map 5} mk_rhs xs xs' alphasAs ctorsAs bound_setss_As) lthy
          |>> split_list o map (fn x => (#2 x, #3 x))
      end;
    val avoidsAs = subst_terms As avoid_terms;

    fun mk_avoid bound_sets x alpha_t avoid_t ctor refresh = split_Nconjs (fbound+1)
      let
        val goal = mk_avoid_term x (list_comb (avoid_t $ x, fsets)) alpha_t ctor bound_sets
          |> HOLogic.mk_Trueprop;
      in
        mk_avoid_tac avoid_defs refresh
          |> prove lthy (x :: fsets) prem_terms_fsets goal
      end;
    val (avoid_freshss, alpha_avoids) =
      @{map 6} mk_avoid bound_setss_As xs alphasAs avoidsAs ctorsAs refreshs
      |> map_split (chop fbound ##> hd);

    (* Define quotient type *)
    fun define_TT name CA alpha_t =
      let
        val rhs = HOLogic.mk_case_prod alpha_t
          |> (fn t => HOLogic.Collect_const (fastype_of t |> domain_type) $ t)
          |> BNF_GFP_Util.mk_quotient (HOLogic.mk_UNIV CA);
      in
        new_typedef (Binding.name name) rhs
          (fn ctxt => EVERY1 [rtac ctxt exI, rtac ctxt @{thm proj_preserves}, rtac ctxt UNIV_I])
      end;
    val ((TT_names, TT_infos), lthy) = @{fold_map 3} define_TT names CAs alphasAs lthy
      |>> split_list;

    val TT_type_definitions = map (#type_definition o snd) TT_infos;

    val CBs = map (fn s => Type (s, As)) TT_names;

    val (TT_Abss, TT_Reps) =
      let
        fun mk_abs_and_rep CA CB info =
          (Const (#Abs_name info, CA --> CB), Const (#Rep_name info, CB --> CA));
      in
        @{map 3} (mk_abs_and_rep o HOLogic.mk_setT) CAs CBs (map fst TT_infos) |> split_list
      end;
    val TT_abss =
      let
        fun mk_TT_abs alpha_t Abs_t CA CB = Const (@{const_name quot_type.abs},
          fastype_of alpha_t --> fastype_of Abs_t --> CA --> CB) $ alpha_t $ Abs_t;
      in
        @{map 4} mk_TT_abs alphasAs TT_Abss CAs CBs
      end;
    val TT_reps =
      let
        fun mk_TT_rep Rep_t CA CB = Const (@{const_name quot_type.rep},
          fastype_of Rep_t --> CB --> CA) $ Rep_t;
      in
        @{map 3} mk_TT_rep TT_Reps CAs CBs
      end;

    val mrbnf_maps_AsBs = mk_mrbnf_terms fst As As CAs CBs mk_map_of_mrbnf I op |> I As;
    val mrbnf_maps_BsAs = mk_mrbnf_terms fst As As CBs CAs mk_map_of_mrbnf I op |> I As;
    val mrbnf_maps_BsBs = mk_mrbnf_terms fst As As CBs CBs mk_map_of_mrbnf I op |> I As;
    val mrbnf_rels_BsBs = mk_mrbnf_terms fst As As CBs CBs mk_mr_rel_of_mrbnf I op |> I As;
    val mrbnf_setss_Bs = mk_mrbnf_terms fst As As CBs CBs mk_sets_of_mrbnf
      (2*fbound + passive + rec_live |> replicate) snd map As;
    val ((free_setss_Bst, bound_setss_Bst), _) = split_setss_transp mrbnf_setss_Bs;
    val ((free_setss_Bs, bound_setss_Bs), rec_setss_Bs) = split_setss mrbnf_setss_Bs;

    val ((((ws, ws'), vs), vs'), frees_lthy) =
      let
        fun mrbnf_rep_T mrbnf_rep_map_As = strip_typeN (2*fbound + passive + rec_live)
          (fastype_of mrbnf_rep_map_As) |> domain_type o snd;
        val mrbnf_rep_Ts = map mrbnf_rep_T mrbnf_maps_BsAs
      in
        mk_Frees "w" CBs frees_lthy
          ||>> mk_Frees "w'" CBs
          ||>> mk_Frees "v" mrbnf_rep_Ts
          ||>> mk_Frees "v'" mrbnf_rep_Ts
      end;

    fun mk_equivp_alpha alpha_t alpha_refl alpha_sym alpha_trans =
      let
        val goal = mk_equivp alpha_t |> HOLogic.mk_Trueprop;
      in
        mk_alpha_equivp_tac alpha_refl alpha_sym alpha_trans
          |> prove_no_prems lthy [] goal
      end;
    val equivp_alphas = @{map 4} mk_equivp_alpha alphasAs alpha_refls alpha_syms alpha_transs;

    fun mk_TT_Quotient TT_type_definition equivp_alpha = @{thm Quotient3_to_Quotient_equivp} OF
      [@{thm quot_type.Quotient} OF [@{thm type_definition_quot_type} OF
        [TT_type_definition, equivp_alpha]], @{thm reflexive}, equivp_alpha];
    val TT_Quotients = map2 mk_TT_Quotient TT_type_definitions equivp_alphas;

    val Quotient_abs_reps = map (fn thm => @{thm Quotient_abs_rep} OF [thm]) TT_Quotients;
    val Quotient_rep_abss = map2 (fn thm1 => fn thm2 => @{thm Quotient_rep_abs} OF [thm1, thm2])
      TT_Quotients alpha_refls;
    val alpha_quotient_syms = map2 (op OF o apsnd single |> curry) alpha_syms Quotient_rep_abss;
    val Quotient_total_abs_eq_iffs = map2 (fn thm1 => fn thm2 => @{thm Quotient_total_abs_eq_iff}
      OF [thm1, @{thm reflpI} OF [thm2]]) TT_Quotients alpha_refls;

    (* Define quotient ctor *)
    val ((cctor_terms, cctor_defs), lthy) =
      let
        fun mk_rhs v TT_abs ctor mrbnf_rec_map_As = TT_abs $ (ctor $ (comb_mrbnf_term
          (map HOLogic.id_const As) TT_reps mrbnf_rec_map_As $ v)) |> absfree (dest_Free v);
      in
        @{fold_map 2} new_definition (map (Binding.name o mk_cctorN) names)
          (@{map 4} mk_rhs vs TT_abss ctorsAs mrbnf_maps_BsAs) lthy
          |>> split_list o map (fn x => (#2 x, #3 x))
      end;
    val cctorsAs = subst_terms As cctor_terms;

    fun mk_TT_abs_ctor x TT_abs ctor cctor mrbnf_abs_map_As cctor_def map_comp mr_rel_map
      TT_Quotient alpha_intro rel_refl_id =
      let
        val goal = mk_Trueprop_eq (TT_abs $ (ctor $ x), cctor $ (comb_mrbnf_term
          (map HOLogic.id_const As) TT_abss mrbnf_abs_map_As $ x));
      in
        mk_TT_abs_ctor_tac cctor_def map_comp TT_Quotient rename_ids mr_rel_map alpha_quotient_syms
          alpha_intro rel_refl_id
          |> prove_no_prems lthy [x] goal
      end;
    val TT_abs_ctors = @{map 11} mk_TT_abs_ctor xs TT_abss ctorsAs cctorsAs mrbnf_maps_AsBs
      cctor_defs map_comps mr_rel_maps TT_Quotients alpha_intros_id mr_rel_refl_ids;

    fun mk_TT_nchotomy v w cctor TT_rep mrbnf_abs_map_As raw_exhaust cctor_def map_comp mr_rel_map
      TT_Quotient alpha_intro rel_refl_id =
      let
        val goal = HOLogic.mk_eq (w, cctor $ v) |> list_exists_free [v] |> HOLogic.mk_Trueprop;

        val rep_exhaust = thm_instantiate_terms lthy [SOME (TT_rep $ w)] raw_exhaust;
        fun mk_exI ct = thm_instantiate_terms lthy [NONE, SOME (comb_mrbnf_term
          (map HOLogic.id_const As) TT_abss mrbnf_abs_map_As $ (Thm.term_of ct))] exI;
      in
        mk_TT_nchotomy_tac rep_exhaust cctor_def map_comp TT_Quotient rename_ids mr_rel_map
          alpha_quotient_syms alpha_intro rel_refl_id mk_exI
          |> prove_no_prems lthy [w] goal
      end;
    val TT_nchotomys = @{map 12} mk_TT_nchotomy vs ws cctorsAs TT_reps mrbnf_maps_AsBs
      raw_exhausts cctor_defs map_comps mr_rel_maps TT_Quotients alpha_intros_id mr_rel_refl_ids;

    (* Define quotient rename *)
    val ((rrename_terms, rrename_defs), lthy) =
      let
        fun mk_rhs w TT_abs TT_rep rename_t = TT_abs $ (list_comb(rename_t, ffs) $ (TT_rep $ w))
          |> fold_rev absfree (map dest_Free (ffs @ [w]));
      in
        @{fold_map 2} new_definition (map (Binding.name o mk_rrenameN) names)
          (@{map 4} mk_rhs ws TT_abss TT_reps renamesAs) lthy
          |>> split_list o map (fn x => (#2 x, #3 x))
      end;
    val rrenamesAs = subst_terms As rrename_terms;

    fun mk_rrename_cctor rrename_t mrbnf_map_BsBs v cctor map_comp cctor_def mr_rel_map TT_Quotient
      rel_refl_id alpha_intro alpha_trans alpha_bij_eq Quotient_rep_abs =
      let
        val recs = map (list_comb o rpair ffs) rrenamesAs;
        val goal = (list_comb (rrename_t, ffs) $ (cctor $ v), cctor $
          (comb_mrbnf_term ffs_ids recs mrbnf_map_BsBs $ v)) |> mk_Trueprop_eq;
        val alpha_trans = alpha_trans OF [alpha_bij_eq RS (iffD2 OF [@{thm _}, Quotient_rep_abs])];
      in
        mk_rrename_cctor_tac rrename_defs cctor_def map_comp mr_rel_map rename_simps rename_ids
          TT_Quotient rel_refl_id alpha_intro alpha_trans alpha_quotient_syms
          |> prove lthy (ffs @ [v]) prem_terms_ffs goal
      end;
    val rrename_cctors = @{map 13} mk_rrename_cctor rrenamesAs mrbnf_maps_BsBs vs cctorsAs
      map_comps cctor_defs mr_rel_maps TT_Quotients mr_rel_refl_ids alpha_intros_id alpha_transs
      alpha_bij_eqs Quotient_rep_abss;

    (* Define quotient FVars *)
    fun define_FFVars i FVars_ts lthy =
      let
        val i = if fbound > 1 then i else 0;
        fun mk_rhs w TT_rep FVars_t = FVars_t $ (TT_rep $ w) |> absfree (dest_Free w);
      in
        @{fold_map 2} new_definition (map (Binding.name o mk_FFVarsN i) names)
          (@{map 3} mk_rhs ws TT_reps FVars_ts) lthy
      end;
    val ((FFVars_termss, FFVars_defss), lthy) = @{fold_map 2} define_FFVars (1 upto fbound) FVarsssAs
      lthy |>> split_list o map (split_list o map (fn x => (#2 x, #3 x)));
    val FFVarsssAs = map (subst_terms As) FFVars_termss;

    fun mk_card_of_FFVars_bound w FFVars_t FFVars_def card_of_FVars_bound =
      let
        val goal = FFVars_t $ w |> mk_bound |> HOLogic.mk_Trueprop;
      in
        (fn ctxt => unfold_tac ctxt [FFVars_def] THEN HEADGOAL (rtac ctxt card_of_FVars_bound))
          |> prove_no_prems lthy [w] goal
      end;
    val card_of_FFVars_boundss = @{map 3} (@{map 4} mk_card_of_FFVars_bound ws) FFVarsssAs
      FFVars_defss card_of_FVars_boundss;

    fun mk_FFVars_cctor FFVars_ts b_vec v cctor FFVars_t Quotient_rep_abs rec_sets free_set
      bound_set alpha_FVars =
      let
        fun add_Diff t = mk_minus t (bound_set $ v);
        fun mk_UN set (w, t) = t $ w |> (absfree o dest_Free) w |> mk_UNION (set $ v);
        val UNs = ws ~~ FFVars_ts |> mk_rec_lives |> map2 mk_UN rec_sets
          |> swap o `(map add_Diff) |-> map_binding_vector b_vec;
        val goal = (FFVars_t $ (cctor $ v), foldl1 mk_union (free_set $ v :: UNs)) |> mk_Trueprop_eq;
      in
        mk_FFVars_cctor_tac alpha_FVars Quotient_rep_abs (flat FFVars_defss) cctor_defs
          (flat FVars_ctorss) set_map
          |> prove_no_prems lthy [v] goal
      end;
    val FFVars_cctorss = @{map 5} (fn FFVars_ts => fn b_rels => @{map 8}
        (mk_FFVars_cctor FFVars_ts b_rels) vs cctorsAs FFVars_ts Quotient_rep_abss rec_setss_Bs)
      FFVarsssAs binding_matrix free_setss_Bst bound_setss_Bst alpha_FVarsss;

    fun mk_FFVars_intros_elims_induct A z b_vec free_sets bound_sets FFVars_ts FVars_intros
      alpha_FVarss FFVars_defs FVars_induct =
      let
        val PTs = map (fn CB => A --> CB --> HOLogic.boolT) CBs;
        val ((Ps, zs'), elim_P) = `(fst o mk_Frees "P" PTs) frees_lthy
          ||>> mk_Frees "z'" (replicate n A)
          ||> fst o yield_singleton (mk_Frees "P") HOLogic.boolT;
        val FVars_abs_reps = map2 (fn thm1 => fn thm2 => thm1 OF [thm2]) alpha_FVarss
          Quotient_rep_abss;

        fun mk_intros_elim ws v cctor FFVars_t free_set bound_set rec_sets w' P FVars_intros
          FVars_abs_rep cctor_def TT_nchotomy =
          let
            val intro_concl = HOLogic.mk_mem (z, FFVars_t $ (cctor $ v));
            val elim_prem = HOLogic.mk_mem (z, FFVars_t $ w') |> HOLogic.mk_Trueprop;
            val elim_concl = HOLogic.mk_eq (w', cctor $ v);
            val elim_varss = [v] :: map (fn w => [w, v]) ws;
            val induct_concls = [] :: (mk_rec_lives Ps |> map2 (fn w => fn P => [P $ z $ w]) ws);
            val induct_concl = P $ z $ (cctor $ v);
            val induct_varss = map (fn varss => varss @ [z]) elim_varss;

            val add_non_mem = HOLogic.mk_mem (z, bound_set $ v) |> HOLogic.mk_not |> curry op ::;
            val concls = mk_rec_lives FFVars_ts
              |> map2 (fn w => fn t => [HOLogic.mk_mem (z, t $ w)]) ws
              |> swap o `(map add_non_mem) |-> map_binding_vector b_vec;
            val rec_ts = [HOLogic.mk_mem (z, free_set $ v)] :: @{map 3}
              (fn t => t $ v |> rpair #> HOLogic.mk_mem #> curry op ::) rec_sets ws concls;

            val intro_goals = map (fn ts => ts @ [intro_concl]) rec_ts
              |> map (foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop);
            val intro_tacs = map (mk_FFVars_intro_tac FFVars_defs cctor_def FVars_abs_rep set_map)
              FVars_intros;
            val intros = @{map 3} (prove_no_prems lthy) induct_varss intro_goals intro_tacs;

            val elim_goal = elim_prem :: (map (foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop o
              (fn ts => ts @ [elim_P]) o curry op :: elim_concl) rec_ts
              |> map2 (fold_rev Logic.all) elim_varss) @ [HOLogic.mk_Trueprop elim_P]
              |> foldr1 Logic.mk_implies;
            val TT_nchotomy_inst = thm_instantiate_terms lthy [SOME w'] TT_nchotomy;
            val elim = mk_FFVars_elim_tac TT_nchotomy_inst (flat FFVars_cctorss)
              |> prove_no_prems lthy [w', z, elim_P] elim_goal;

            val induct_prems = rec_ts
              |> map2 (fn ts2 => fn ts1 => ts1 @ ts2 @ [induct_concl]) induct_concls
              |> map (foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop)
              |> map2 (fold_rev Logic.all) induct_varss;
          in
            ((intros, elim), induct_prems)
          end;
        val (intro_elims, induct_prems) = @{map 12} (mk_rec_lives ws |> mk_intros_elim) vs cctorsAs
          FFVars_ts free_sets bound_sets rec_setss_Bs ws' Ps (chop_groups (rec_live+1) FVars_intros)
          FVars_abs_reps cctor_defs TT_nchotomys |> split_list ||> flat |>> apfst flat o split_list;

        fun mk_imp FFVars_t z' w P = HOLogic.mk_imp (HOLogic.mk_mem (z', FFVars_t $ w), P $ z' $ w);
        val imps = @{map 4} mk_imp FFVars_ts zs' ws Ps;
        val induct_goal = mk_conjs imps |> HOLogic.mk_Trueprop;

        val conj_imps = let val dummies = Term.dummy_pattern HOLogic.boolT |> replicate n;
          in map2 (fn i => fn t => nth_map i (K t) dummies |> mk_conjs) (0 upto n-1) imps end;
        fun mk_induct_inst TT_Quotient alpha_refl conj_imp w = (@{thm Quotient_total_abs_induct} OF
          [TT_Quotient, @{thm reflpI} OF [alpha_refl]])
          |> thm_instantiate_dummy_terms lthy [SOME (absfree (dest_Free w) conj_imp), SOME w];
        val induct_insts = @{map 4} mk_induct_inst TT_Quotients alpha_refls conj_imps ws;
      in
        (intro_elims,
          mk_FFVars_induct_tac mutual induct_insts FFVars_defs cctor_defs FVars_abs_reps
            FVars_induct TT_abs_ctors set_map
            |> prove lthy (zs' @ ws @ Ps) induct_prems induct_goal
            |> (if mutual then I else (fn thm => Drule.rotate_prems ~1 (thm RS mp))))
      end;
    val ((FFVars_intross, FFVars_elimss), FFVars_inducts) = @{map 10} mk_FFVars_intros_elims_induct
      (take fbound As) zs binding_matrix free_setss_Bst bound_setss_Bst FFVarsssAs FVars_intross
      alpha_FVarsss FFVars_defss FVars_inducts |> split_list |>> split_list;

    fun mk_TT_inject0 v v' cctor mrbnf_map_BsBs bound_sets rec_sets mr_rel_eq mr_rel_map cctor_def
      abs_eq_iff alpha_elim set_map mr_rel_mono_strong0 alpha_intro =
      let
        val FFVarsBs =
          let
            fun mk_zips FFVars_ts = map (op $ o rpair v) rec_sets ~~ mk_rec_lives FFVars_ts;
            fun mk_bound_minus bound_set t = mk_minus t (bound_set $ v);
            fun mk_UNION_term bound_set FFVars_ts b_rels = map (nth (mk_zips FFVars_ts)
              #-> mk_UNION) b_rels |> map (mk_bound_minus bound_set)
              |> foldl1 mk_union;
          in
            @{map 3} mk_UNION_term bound_sets FFVarsssAs binding_relation
          end;
        val prems1 = map2 mk_id_on FFVarsBs ffs;

        val rrename_consts = rrenamesAs ~~ map HOLogic.id_const CBs |> mk_rec_lives;
        val rrename_args = apply2 (replicate rec_live |> map) (fids, ffs)
          |-> transpose oo map_binding_matrix
          |> map2 (fn b => if b then K NONE else SOME) no_bindings;
        fun mk_rec_rel (_, id) NONE = id
          | mk_rec_rel (rrename_t, _) (SOME fs) = list_comb (rrename_t, fs);
        val prem0 = HOLogic.mk_eq (list_comb (mrbnf_map_BsBs, map HOLogic.id_const As @ ffs @
          map2 mk_rec_rel rrename_consts rrename_args) $ v, v');

        val goal = mk_Trueprop_eq (HOLogic.mk_eq (cctor $ v, cctor $ v'),
          map HOLogic.dest_Trueprop prem_terms_ffs @ prems1 @ [prem0] |> mk_conjs
            |> list_exists_free ffs);
        val rotated_mr_rel_mono_strong0 = Drule.rotate_prems (6*fbound) mr_rel_mono_strong0;
        val Quotient_rel_reps = map (fn thm => @{thm Quotient_rel_rep} OF [thm] RS iffD1)
          TT_Quotients;
        val alpha_sym_transs = map2 (fn thm1 => fn thm2 => thm1 OF [Drule.rotate_prems 1 thm2])
          alpha_syms alpha_transs;
      in
        mk_TT_inject0_tac fbound alpha_intro mr_rel_eq cctor_def abs_eq_iff mr_rel_map alpha_elim
          (flat FFVars_defss |> map (fn thm => thm RS @{thm symmetric})) set_map rrename_defs
          Quotient_rep_abss Quotient_rel_reps rotated_mr_rel_mono_strong0 alpha_syms
          alpha_sym_transs alpha_quotient_syms alpha_refls
          |> prove_no_prems lthy [v, v'] goal
      end;
    val TT_injects0 = @{map 14} mk_TT_inject0 vs vs' cctorsAs mrbnf_maps_BsBs bound_setss_Bs
      rec_setss_Bs mr_rel_eqs mr_rel_maps cctor_defs Quotient_total_abs_eq_iffs alpha_elims set_maps
      mr_rel_mono_strong0s alpha_intros;

    (* Define quotient avoid *)
    val ((aavoid_terms, aavoid_defs), lthy) =
      let
        fun mk_rhs v avoid_t mrbnf_map_AsBs mrbnf_map_BsAs =
          let
            val ids = map HOLogic.id_const As;
            val abs_map = comb_mrbnf_term ids TT_abss mrbnf_map_AsBs;
            val rep_map = comb_mrbnf_term ids TT_reps mrbnf_map_BsAs;
          in
            abs_map $ (list_comb (avoid_t $ (rep_map $ v), fsets))
              |> fold_rev (absfree o dest_Free) (v :: fsets)
          end;
      in
        @{fold_map 2} new_definition (map (Binding.name o mk_aavoidN) names)
          (@{map 4} mk_rhs vs avoidsAs mrbnf_maps_AsBs mrbnf_maps_BsAs) lthy
          |>> split_list o map (fn x => (#2 x, #3 x))
      end;
    val aavoidsAs = subst_terms As aavoid_terms;

    fun mk_aavoid_term f v v' cctor bound_sets =
      let
        fun mk_eq set_t fset = HOLogic.mk_eq (mk_inter (set_t $ v, fset),
          Const (@{const_name bot}, fastype_of fset));
      in
        map2 mk_eq bound_sets fsets @ [HOLogic.mk_eq (cctor $ v, v')] |> mk_conjs o f
      end;

    fun mk_aavoid v aavoid_t cctor bound_sets aavoid_def cctor_def avoid_freshs map_comp set_map
      mr_rel_map rel_refl_id TT_Quotient alpha_trans alpha_intro_id alpha_sym alpha_avoid =
      let
        val goal = mk_aavoid_term I (list_comb (aavoid_t $ v, fsets)) (cctor $ v) cctor bound_sets
          |> HOLogic.mk_Trueprop;
      in
        mk_aavoid_tac aavoid_def cctor_def map_comp TT_Quotient set_map mr_rel_map rename_ids
          alpha_sym rel_refl_id avoid_freshs Quotient_rep_abss alpha_trans alpha_intro_id
          alpha_avoid
          |> prove lthy (v :: fsets) prem_terms_fsets goal
          |> split_Nconjs (fbound+1)
      end;
    val (aavoid_freshss, alpha_aavoids) =
      @{map 16} mk_aavoid vs aavoidsAs cctorsAs bound_setss_Bs aavoid_defs cctor_defs
      avoid_freshss map_comps set_maps mr_rel_maps mr_rel_refl_ids TT_Quotients alpha_transs
      alpha_intros_id alpha_syms alpha_avoids
      |> map_split (chop fbound ##> hd);

    fun mk_TT_fresh_cases v w cctor bound_sets TT_nchotomy alpha_aavoid aavoid_freshs =
      let
        val mk_sym_term = swap o chop fbound #>> HOLogic.mk_eq o swap o HOLogic.dest_eq o the_single
          #> op ::;
        val goal = mk_aavoid_term mk_sym_term v w cctor bound_sets |> list_exists_free [v]
          |> HOLogic.mk_Trueprop;
        val insert_nchotomy = thm_instantiate_terms lthy [SOME w] TT_nchotomy;
      in
        mk_TT_fresh_cases_tac insert_nchotomy alpha_aavoid aavoid_freshs
          |> prove lthy (w :: fsets) prem_terms_fsets goal
          |> `(fn thm => unfold_thms lthy @{thms conj_imp_eq_imp_imp} (thm RS exE))
      end;
    val (TT_fresh_cases, TT_fresh_nchotomys) = @{map 7} mk_TT_fresh_cases vs ws cctorsAs
      bound_setss_Bs TT_nchotomys alpha_aavoids aavoid_freshss |> split_list;

    val (TT_existential_co_induct, TT_fresh_co_induct_param, TT_fresh_induct_param_no_clash_opt,
      subshapess_opt,
      TT_subshape_induct_opt, wf_subshapess_opt, set_subshape_imagesss_opt, set_subshapesss_opt,
      TT_fresh_co_induct, TT_plain_co_induct, lthy) = if co
      then let
          (* Define coinductive predicate alpha' *)
          val (alpha's_invar_result, (alpha'sAs, _ (*alpha's*)), lthy) =
            let
              val bs = map (Binding.name o mk_alpha'N) names;
              val Ts = map (fn CA => CA --> CA --> HOLogic.boolT) CAs;
              val inductive_flags = {quiet_mode = true, verbose = false, alt_name = Binding.empty,
                coind = true, no_elim = false, no_ind = false, skip_mono = false};
              val alpha'_ts = map2 (Free oo pair o Binding.name_of) bs Ts;

              fun mk_term x x' ctor alpha'_t bound_sets rec_sets mrbnf_rel_AsAs =
                let
                  fun mk_FVarsBs x =
                    let
                      fun mk_zips FVars_ts = map (op $ o rpair x) rec_sets ~~ mk_rec_lives FVars_ts;
                      fun mk_bound_minus bound_set t = mk_minus t (bound_set $ x);
                      fun mk_UNION_term bound_set FVars_ts b_rels = map (nth (mk_zips FVars_ts)
                        #-> mk_UNION) b_rels |> map (mk_bound_minus bound_set)
                        |> foldl1 mk_union;
                    in
                      @{map 3} mk_UNION_term bound_sets FVarsssAs binding_relation
                    end;
                  val prems1 = map2 mk_id_on (mk_FVarsBs x) ffs;
                  val prems2 = map2 mk_id_on (mk_FVarsBs x') fgs;

                  val recs_consts = ys ~~ ys' ~~ renamesAs ~~ alpha'_ts |> mk_rec_lives;
                  val rename_args = apply2 (replicate rec_live |> map) (fids ~~ fids, ffs ~~ fgs)
                    |-> transpose oo map_binding_matrix
                    |> map2 (fn b => if b then K NONE else SOME) no_bindings
                    |> map (Option.map split_list);
                  fun mk_rec_rel (_, alpha'_t) NONE = alpha'_t
                    | mk_rec_rel (((y, y'), rename_t), alpha'_t) (SOME (fs, gs)) = alpha'_t $
                      (list_comb (rename_t, fs) $ y) $ (list_comb (rename_t, gs) $ y')
                      |> fold_rev (absfree o dest_Free) [y, y'];
                  val ideqs = map2 I (replicate free HOLogic.id_const @
                    replicate plive HOLogic.eq_const @ replicate pbound HOLogic.id_const) As;
                  val prem0 = list_comb (mrbnf_rel_AsAs, ideqs @
                    map2 (mk_inv #> curry HOLogic.mk_comp) fgs ffs @
                    map2 mk_rec_rel recs_consts rename_args) $ x $ x';
                  val concl = alpha'_t $ (ctor $ x) $ (ctor $ x');
                in
                  map HOLogic.mk_Trueprop prems1 @ [foldr1 Logic.mk_implies
                    (prems2 @ [prem0, concl] |> map HOLogic.mk_Trueprop) |> add_prems fgs]
                    |> foldr1 Logic.mk_implies |> add_prems ffs
                end;
              val terms = @{map 7} mk_term xs xs' ctorsAs alpha'_ts bound_setss_As rec_setss_As
                mrbnf_rels_AsAs;

              fun mk_mono mr_rel_mono supp_comp_bound = mr_rel_mono OF replicate fbound
                @{thm supp_id_bound} @ (replicate fbound [@{thm bij_comp[OF _ bij_imp_bij_inv]},
                  supp_comp_bound OF [@{thm _}, @{thm supp_inv_bound}]] |> flat);
              val monos = map2 mk_mono mr_rel_monos supp_comp_bounds @ @{thms conj_context_mono};

              val (invar_result_raw, (new_lthy, lthy)) = lthy
                |> Local_Theory.begin_nested |> snd
                |> Inductive.add_inductive inductive_flags (map2 (rpair NoSyn oo pair) bs Ts) []
                  (map (pair Binding.empty_atts) terms) monos
                ||> `Local_Theory.end_nested;

              val phi = Proof_Context.export_morphism lthy new_lthy;
              val invar_result = Inductive.transform_result phi invar_result_raw;
              val frees_freesAs = map (Morphism.term phi) alpha'_ts |> `(subst_terms As);
            in
              (invar_result, frees_freesAs, new_lthy)
            end;

          val alpha'_coinduct = #induct alpha's_invar_result;
          val alpha'_elims = #elims alpha's_invar_result;

          val alpha'_bij_eq_invs =
            let
              fun mk_eq alpha'_t rename_t y y' = HOLogic.mk_imp
                (alpha'_t $ (list_comb (rename_t, ffs) $ y) $ y',
                  alpha'_t $ y $ (list_comb (rename_t, map mk_inv ffs) $ y'));
              val goal = @{map 4} mk_eq alpha'sAs renamesAs ys ys' |> mk_conjs
                |> HOLogic.mk_Trueprop;

              fun mk_rel alpha'_t rename_t y y' = alpha'_t $ (list_comb (rename_t, ffs) $ y) $
                (list_comb (rename_t, ffs) $ y') |> SOME o fold_rev (absfree o dest_Free) [y, y'];
              val alpha'_coinduct_inst = (thm_instantiate_terms lthy
                (@{map 4} mk_rel alpha'sAs renamesAs ys ys') alpha'_coinduct)
                |> (if mutual then (fn thm => meta_mp OF [@{thm _}, thm]) else I);
              val imp_forward = if mutual then @{thm _} else (thm_instantiate_fixed_terms lthy
                [hd alpha'sAs $ (list_comb (hd renamesAs, ffs) $ hd ys) $
                  (list_comb (hd renamesAs, ffs) $ hd ys') |> SOME, hd alpha'sAs $ (hd ys) $
                  (hd ys') |> SOME] [hd ys, hd ys'] @{thm imp_forward})
                |> Drule.rearrange_prems [2,1,0];

              fun mk_exI f g = thm_instantiate_terms lthy [NONE,
                SOME (HOLogic.mk_comp (mk_inv f, HOLogic.mk_comp (g, f)))] exI;
              fun mk_exIs fs gs = map (map2 mk_exI ffs) [fs, gs] |> flat;
            in
              mk_alpha'_bij_eq_invs_tac fbound alpha'_coinduct_inst raw_injects mk_exIs mutual
              imp_forward supp_comp_bounds rename_simps (flat FVars_renamess) rename_comps
              alpha'_elims raw_nchotomys mr_rel_maps set_maps mr_rel_mono_strong0s rename_ids
                |> prove lthy (ffs @ ys @ ys') prem_terms_ffs goal
                |> split_conjs
                |> map (fn thm => thm RS mp)
            end;

          fun mk_alpha'_bij_eq_inv' y y' alpha'_t rename_t alpha'_bij_eq_inv rename_id
            rename_comp =
            let
              val rename = list_comb (rename_t, ffs) $ y';
              val inv_rename = list_comb (rename_t, map mk_inv ffs);
              val goal = [alpha'_t $ y $ rename, alpha'_t $ (inv_rename $ y) $ y']
                |> map HOLogic.mk_Trueprop |> foldr1 Logic.mk_implies;

              val arg_cong_inst = thm_instantiate_terms lthy [SOME y', SOME (inv_rename $ rename),
                SOME (alpha'_t $ (inv_rename $ y) $ y' |> absfree (dest_Free y'))] @{thm arg_cong}
                RS iffD2 OF [@{thm _}, alpha'_bij_eq_inv];
            in
              mk_alpha'_bij_eq_inv'_tac arg_cong_inst rename_id rename_comp
                |> prove lthy (ffs @ [y, y']) prem_terms_ffs goal
            end;
          val alpha'_bij_eq_inv's = @{map 7} mk_alpha'_bij_eq_inv' ys ys' alpha'sAs renamesAs
            alpha'_bij_eq_invs rename_ids rename_comps;

          fun mk_alpha'_FVars_les n z FVars_ts FVars_induct set_transfers =
            let
              fun mk_eq y y' alpha'_t FVars_t = HOLogic.mk_imp (HOLogic.mk_mem (z, FVars_t $ y),
                HOLogic.mk_imp (alpha'_t $ y $ y', HOLogic.mk_mem (z, FVars_t $ y'))
                  |> list_all_free [y']);
              val eqs = @{map 4} mk_eq ys ys' alpha'sAs FVars_ts;
              val goal = mk_conjs eqs |> HOLogic.mk_Trueprop;

              val zset = mk_Frees "zs" [fastype_of z |> HOLogic.mk_setT] frees_lthy
                |> the_single o fst;
              fun mk_arg_cong f g =
                thm_instantiate_fixed_terms lthy [SOME (mk_inv f $ (g $ z)), SOME z, SOME
                  (HOLogic.mk_mem (z, zset) |> absfree (dest_Free z))] [z, zset] arg_cong RS iffD2;
            in
              mk_alpha'_FVars_les_tac mutual fbound (n-1) (rec_live+1)
                (mk_rec_lives (alpha'_bij_eq_invs ~~ rename_comps)) FVars_induct alpha'_elims
                raw_injects (flat FVars_renamess) (flat FVars_ctorss) set_transfers mk_arg_cong
                supp_comp_bounds
                |> prove_no_prems lthy (ys @ [z]) goal
                |> split_conjs
                |> map (fn thm => Drule.rotate_prems 1 (thm RS mp RS spec RS mp))
            end;
          val alpha'_FVars_less =
            let
              fun zip_opt (xs, NONE) = map (rpair NONE) xs
                | zip_opt (xs, SOME ys) = xs ~~ map SOME ys;
              fun add_bound_sett rec_settss free_setts bound_setts b_vec =
                map (rpair NONE) rec_settss |> swap o `(SOME bound_setts |> map o apsnd o K)
                  |-> map_binding_vector b_vec |> map zip_opt
                  |> (map2 (curry op:: o rpair NONE) free_setts) o transpose;
              val set_transferss = @{map 3} (add_bound_sett rec_settss) free_settss bound_settss
                binding_matrix;
            in
              @{map 5} mk_alpha'_FVars_les (1 upto fbound) zs FVarsssAs FVars_inducts set_transferss
            end;

          val alpha_imp_alpha's =
            let
              fun mk_eq alpha_t alpha'_t y y' = HOLogic.mk_imp (alpha_t $ y $ y', alpha'_t $ y $ y')
                |> list_all_free [y, y'];
              val goal = @{map 4} mk_eq alphasAs alpha'sAs ys ys' |> HOLogic.mk_Trueprop o mk_conjs;
            in
              mk_alpha_imp_alpha's_tac mutual fbound alpha'_coinduct raw_injects rename_ids
                alpha_elims mr_rel_mono_strong0s
                |> prove_no_prems lthy [] goal
                |> split_conjs
                |> map (fn thm => thm RS @{thm spec2})
            end;

          val alpha'_imp_alphas =
            let
              fun mk_eq alpha_t alpha'_t y y' = HOLogic.mk_imp (alpha'_t $ y $ y', alpha_t $ y $ y')
                |> list_all_free [y, y'];
              val goal = @{map 4} mk_eq alphasAs alpha'sAs ys ys' |> HOLogic.mk_Trueprop o mk_conjs;

              val settss = map2 (curry op ::) (transpose bound_settss |> flat) (map_product
                (fn xs => fn bs => filter_like bs I xs) (transpose rec_settss) binding_matrix);

              fun mk_arg_cong z h f g =
                thm_instantiate_fixed_terms lthy [SOME (mk_inv f $ (g $ z)), SOME z, SOME
                  (HOLogic.mk_eq (h $ z, z) |> absfree (dest_Free z))] [z, h] arg_cong RS iffD2;
              val mk_arg_congs = @{map 4} mk_arg_cong zs fgs;
            in
              mk_alpha'_imp_alphas_tac fbound alpha_coinduct supp_comp_bounds mk_arg_congs mutual
                (flat FVars_renamess) alpha'_bij_eq_invs alpha'_bij_eq_inv's
                (flat alpha'_FVars_less) rename_comps raw_injects alpha'_elims
                mr_rel_mono_strong0s settss
                |> prove_no_prems lthy [] goal
                |> split_conjs
                |> map (fn thm => thm RS @{thm spec2})
            end;

          val alpha_alpha's = map2
            (fn thm1 => fn thm2 => @{thm iff_conv_conj_imp[THEN iffD2, OF conjI]} OF [thm1, thm2])
            alpha_imp_alpha's alpha'_imp_alphas;

          val ((Rs, Ss), frees_lthy) = frees_lthy
            |> mk_Frees "R" (map (fn CB => CB --> CB --> paramT --> HOLogic.boolT) CBs)
            ||>> mk_Frees "S" (map (fn CB => CB --> CB --> HOLogic.boolT) CBs);

          val TT_existential_coinduct =
            let
              fun mk_eq w w' S = HOLogic.mk_imp (S $ w $ w', HOLogic.mk_eq (w, w'))
                |> list_all_free [w, w'];
              val goal = @{map 3} mk_eq ws ws' Ss |> mk_conjs |> HOLogic.mk_Trueprop;

              fun mk_rel S w w' = HOLogic.mk_disj (S $ w $ w', HOLogic.mk_eq (w, w'))
                |> fold_rev (absfree o dest_Free) [w, w'];
              val rels = @{map 3} mk_rel Ss ws ws';
              val ideqs = map2 I (replicate free HOLogic.id_const @ replicate plive HOLogic.eq_const
                @ replicate pbound HOLogic.id_const) As;
              val (us, us') = frees_lthy
                |> mk_Frees "u" (map fastype_of vs)
                ||> fst o mk_Frees "u'" (map fastype_of vs');

              fun mk_hyp mrbnf_rel_BsBs u u' v v' S cctor = [S $ (cctor $ v) $ (cctor $ v'),
                [HOLogic.mk_eq (cctor $ u, cctor $ v), HOLogic.mk_eq (cctor $ u', cctor $ v'),
                  comb_mrbnf_term ideqs rels mrbnf_rel_BsBs $ u $ u']
                  |> mk_conjs |> list_exists_free [u, u']] |> map HOLogic.mk_Trueprop
                |> foldr1 Logic.mk_implies |> fold_rev Logic.all [v, v'];
              val hyps = @{map 7} mk_hyp mrbnf_rels_BsBs us us' vs vs' Ss cctorsAs;

              fun mk_rep_eq y y' S TT_abs alpha_t = HOLogic.mk_imp
                (S $ (TT_abs $ y) $ (TT_abs $ y'), alpha_t $ y $ y') |> list_all_free [y, y'];
              val rep_meta_mp = thm_instantiate_terms lthy [@{map 5} mk_rep_eq ys ys' Ss
                TT_abss alphasAs |> mk_conjs |> HOLogic.mk_Trueprop |> SOME] meta_mp;

              fun mk_abs_rel y y' S TT_abs alpha_t = HOLogic.mk_disj
                (S $ (TT_abs $ y) $ (TT_abs $ y'), alpha_t $ y $ y')
                |> fold_rev (absfree o dest_Free) [y, y'];
              val abs_rels = @{map 5} mk_abs_rel ys ys' Ss TT_abss alphasAs;
              fun mk_abs_meta_mp mrbnf_map_BsAs mrbnf_rel_AsAs mrbnf_rel_BsBs v v' =
                thm_instantiate_fixed_terms lthy
                  ([comb_mrbnf_term ideqs rels mrbnf_rel_BsBs $ v $ v',
                    comb_mrbnf_term ideqs abs_rels mrbnf_rel_AsAs $
                      (comb_mrbnf_term (map HOLogic.id_const As) TT_reps mrbnf_map_BsAs $ v) $
                      (comb_mrbnf_term (map HOLogic.id_const As) TT_reps mrbnf_map_BsAs $ v')]
                    |> map (SOME o HOLogic.mk_Trueprop)) [v, v'] meta_mp |> Drule.rotate_prems ~1;
              val abs_meta_mps = @{map 5} mk_abs_meta_mp mrbnf_maps_BsAs mrbnf_rels_AsAs
                mrbnf_rels_BsBs vs vs';

              fun mk_allE TT_rep w = thm_instantiate_fixed_terms lthy [NONE, SOME (TT_rep $ w)] [w]
                allE;
              val allE_insts = map2 mk_allE TT_reps ws;
            in
              mk_TT_existential_coinduct_tac fbound (plive + rec_live) raw_injects rep_meta_mp
                Quotient_abs_reps alpha_refls Quotient_total_abs_eq_iffs supp_comp_bounds allE_insts
                alpha_alpha's alpha'_coinduct raw_nchotomys TT_abs_ctors cctor_defs alpha_syms
                alpha_elims abs_meta_mps mr_rel_maps mr_rel_mono_strong_ids mr_rel_mono_strong0s
                mr_le_rel_OOs mr_rel_flips mutual
                |> prove lthy Ss hyps goal
            end;

          val TT_fresh_coinduct_param =
            let
              val bex_rho_param = absfree (dest_Free rho) #> mk_Bex param;
              fun mk_bex_Rww' R w w' = R $ w $ w' $ rho |> bex_rho_param;
              fun mk_eq w w' R = HOLogic.mk_imp (mk_bex_Rww' R w w', HOLogic.mk_eq (w, w'))
                |> list_all_free [w, w'];
              val goal = @{map 3} mk_eq ws ws' Rs |> mk_conjs |> HOLogic.mk_Trueprop;

              val params = map (fn varsOf => [HOLogic.mk_mem (rho, param), varsOf $ rho |> mk_bound]
                |> map HOLogic.mk_Trueprop |> foldr1 Logic.mk_implies |> Logic.all rho) varsOfs;
              fun mk_not_varsOf z set varsOf v = [HOLogic.mk_mem (z, set $ v),
                HOLogic.mk_mem (z, varsOf $ rho) |> HOLogic.mk_not] |> map HOLogic.mk_Trueprop
                |> foldr1 Logic.mk_implies |> Logic.all z;
              fun mk_not_varsOfs v v' sets = @{map 3} (fn z => fn set => fn varsOf =>
                map (mk_not_varsOf z set varsOf) [v, v']) zs sets varsOfs |> flat;

              fun mk_rel R w w' = HOLogic.mk_disj (mk_bex_Rww' R w w', HOLogic.mk_eq (w, w'))
                |> fold_rev (absfree o dest_Free) [w, w'];
              val rels = @{map 3} mk_rel Rs ws ws';
              val ideqs = map2 I (replicate free HOLogic.id_const @ replicate plive HOLogic.eq_const
                @ replicate pbound HOLogic.id_const) As;

              fun mk_hyp mrbnf_rel_BsBs v v' R cctor sets = [R $ (cctor $ v) $ (cctor $ v') $ rho
                  |> HOLogic.mk_Trueprop] @ mk_not_varsOfs v v' sets @
                ([HOLogic.mk_mem (rho, param), comb_mrbnf_term ideqs rels mrbnf_rel_BsBs $ v $ v']
                  |> map HOLogic.mk_Trueprop) |> foldr1 Logic.mk_implies
                |> fold_rev Logic.all [v, v', rho];
              val hyps = @{map 6} mk_hyp mrbnf_rels_BsBs vs vs' Rs cctorsAs bound_setss_Bs;
            in
              mk_TT_fresh_coinduct_param_tac fbound TT_existential_coinduct TT_fresh_cases
                |> prove lthy (param :: varsOfs @ Rs) (params @ hyps) goal
            end;

          val TT_fresh_coinduct = thm_instantiate_fixed_terms lthy (HOLogic.mk_UNIV paramT ::
            map (absfree (dest_Free rho)) fsets @ @{map 3} (fn S => fn w => fn w' => S $ w $ w'
              |> fold_rev (absfree o dest_Free) [w, w', rho]) Ss ws ws' |> map SOME) (fsets @ Ss)
            TT_fresh_coinduct_param |> full_simplify lthy;

          val TT_plain_coinduct = (TT_fresh_coinduct OF
            (replicate fbound @{thm supp_id_bound[unfolded supp_id]})) |> full_simplify lthy;

          fun after_qed thm = if mutual then thm else
            Drule.rotate_prems ~1 (thm RS @{thm spec2} RS mp);
        in
          (after_qed TT_existential_coinduct, after_qed TT_fresh_coinduct_param, NONE, NONE, NONE,
            NONE, NONE, NONE, after_qed TT_fresh_coinduct, after_qed TT_plain_coinduct, lthy)
        end
      else let
          (* Define inductive predicate subshape *)
          fun define_subshape name2 CA2 ctor x name1 CA1 alpha_t rename_t y y' sets lthy =
            let
              val b = mk_subshapeN name1 name2 |> Binding.name;
              val T = CA1 --> CA2 --> HOLogic.boolT;
              val inductive_flags = {quiet_mode = true, verbose = false, alt_name = Binding.empty,
                coind = false, no_elim = false, no_ind = false, skip_mono = false};
              val subshape_t = Free (Binding.name_of b, T);

              val concl = subshape_t $ y $ (ctor $ x);
              val prem1 = alpha_t $ (list_comb (rename_t, ffs) $ y) $ y';
              val prem2 = HOLogic.mk_mem (y', if length sets = 0
                then Const (@{const_name bot}, fastype_of y' |> HOLogic.mk_setT)
                else map (fn t => t $ x) sets |> foldl1 mk_union);
              val term = prem_terms_ffs @ map HOLogic.mk_Trueprop [prem1, prem2, concl]
                |> foldr1 Logic.mk_implies;

              val (invar_result_raw, (new_lthy, lthy)) = lthy
                |> Local_Theory.begin_nested |> snd
                |> Inductive.add_inductive inductive_flags [((b, T), NoSyn)] []
                  (map (pair Binding.empty_atts) [term]) []
                ||> `Local_Theory.end_nested;

              val phi = Proof_Context.export_morphism lthy new_lthy;
              val invar_result = Inductive.transform_result phi invar_result_raw;
              val subshape_subshapeAs = Morphism.term phi subshape_t
                |> `(subst_terms As |> singleton);
            in
              ((invar_result, subshape_subshapeAs), new_lthy)
            end;
          fun define_subshapes name2 CA2 ctor x = apfst (split_list ##> split_list) oo
            @{fold_map 7} (define_subshape name2 CA2 ctor x) names CAs alphasAs renamesAs ys ys';
          val ((subshape_invar_resultss, (subshapessAs, _ (*subshapess*))), lthy) =
            @{fold_map 5} define_subshapes names CAs ctorsAs xs (map dest_rec_lives rec_setss_As)
              lthy |>> apsnd split_list o split_list;

          val subshape_elimss = (the_single o #elims |> map o map) subshape_invar_resultss;
          val subshape_intross = (the_single o #intrs |> map o map) subshape_invar_resultss;

          val subshape_induct_raw =
            let
              val Ps = mk_Frees "P" (map (fn T => T --> HOLogic.boolT) CAs) frees_lthy |> fst;
              fun mk_hyp_prem y y' P subshape_t = (subshape_t $ y' $ y, P $ y')
                |> apply2 HOLogic.mk_Trueprop |> Logic.mk_implies |> Logic.all y';
              fun mk_hyp P y subshape_ts = @{map 3} (mk_hyp_prem y) ys' Ps subshape_ts @
                [P $ y |> HOLogic.mk_Trueprop] |> foldr1 Logic.mk_implies |> Logic.all y;
              val hyps = @{map 3} mk_hyp Ps ys subshapessAs;

              fun mk_eq P y y' alpha_t rename_t = map HOLogic.dest_Trueprop prem_terms_ffs @
                [alpha_t $ (list_comb (rename_t, ffs) $ y) $ y', P $ y'] |> foldr1 HOLogic.mk_imp
                |> list_all_free (ffs @ [y']);
              val eqs = @{map 5} mk_eq Ps ys ys' alphasAs renamesAs;
              val common_co_induct_inst = mk_common_co_induct_inst frees_lthy CAs lthy eqs ys;
              val goal = mk_conjs eqs |> HOLogic.mk_Trueprop;

              fun mk_prem ctxt fs hs g_opts prem = thm_instantiate_terms lthy (NONE :: @{map 3}
                  (fn f => fn g_opt => fn h => HOLogic.mk_comp (mk_inv h, case g_opt of NONE => f
                    | SOME g => HOLogic.mk_comp (g, f)) |> SOME) fs g_opts hs)
                (Object_Logic.rulify ctxt prem);
              fun mk_prems i ctxt fs gs hs prems = map2 (mk_prem ctxt fs hs)
                (apply2 (replicate rec_live |> map) (replicate fbound NONE, map SOME gs)
                  |-> transpose oo map_binding_matrix) prems |> dest_rec_lives
                  |> (fn xs => nth xs i);
              val mk_prem_funs = map mk_prems (0 upto n-1);

              fun mk_rename_comp fs gs rename_comp = thm_instantiate_terms lthy (map SOME (fs @ gs))
                (rename_comp RS sym) |> unfold_thms lthy @{thms id_o};
              fun map_all_no_binding xs = all_bindings ~~ no_bindings ~~ xs |> dest_rec_lives
                |> (map o map) (fn ((b1, b2), x) => if b1 orelse b2 then [] else [x]);
              fun mk_rename_comps i fs gs = map2 (mk_rename_comp fs) (apply2 (replicate rec_live
                |> map) (map (HOLogic.id_const o domain_type o fastype_of) gs, gs)
                  |-> transpose oo map_binding_matrix) (mk_rec_lives rename_comps)
                |> map_all_no_binding |> (fn xs => nth xs i);
              val mk_rename_comp_funs = map mk_rename_comps (0 upto n-1);

              fun mk_sett sett = Drule.rotate_prems ~1 (sett RS rel_funD);
              val settsss = map (dest_rec_lives o map mk_sett o take rec_live o drop
                (2*fbound+passive)) settss;

              fun mk_alpha_bij_eq_inv alpha_bij_eq_inv = alpha_bij_eq_inv OF (replicate fbound
                @{thms bij_imp_bij_inv supp_inv_bound} |> flat);
              val alpha_bij_eq_invs = map mk_alpha_bij_eq_inv alpha_bij_eq_invs;
            in
              mk_subshape_induct_raw_tac fbound rec_live rename_simps raw_injects rename_comps
                alpha_bij_eq_invs alpha_transs alpha_syms mk_prem_funs mk_rename_comp_funs
                common_co_induct_inst mr_rel_maps supp_comp_bounds alpha_elims subshape_elimss
                settsss
                |> prove lthy (Ps @ ys) hyps goal
            end;

          val subshape_induct =
            let
              val Ps = mk_Frees "P" (map (fn T => T --> HOLogic.boolT) CAs) frees_lthy |> fst;
              fun mk_hyp_prem y y' P subshape_t = (subshape_t $ y' $ y, P $ y')
                |> apply2 HOLogic.mk_Trueprop |> Logic.mk_implies |> Logic.all y';
              fun mk_hyp P y subshape_ts = @{map 3} (mk_hyp_prem y) ys' Ps subshape_ts @
                [P $ y |> HOLogic.mk_Trueprop] |> foldr1 Logic.mk_implies |> Logic.all y;
              val hyps = @{map 3} mk_hyp Ps ys subshapessAs;

              val goal = map2 (curry op $) Ps ys |> HOLogic.mk_Trueprop o mk_conjs;
              val subshape_induct_raw_inst = thm_instantiate_terms lthy (map SOME Ps)
                subshape_induct_raw;
              val meta_spec_ys = map (fn y => thm_instantiate_terms lthy [NONE, SOME y] meta_spec)
                ys;
              val spec_ys = map (fn y => thm_instantiate_terms lthy [NONE, SOME y] spec) ys;
            in
              mk_subshape_induct_tac n subshape_induct_raw_inst meta_spec_ys spec_ys rename_ids
                alpha_refls
                |> prove lthy (Ps @ ys) hyps goal
            end;

          fun mk_wf_subshape CA1 CA2 subshape_t =
            let
              val T = HOLogic.mk_prodT (CA1, CA2)
              val goal = HOLogic.mk_Trueprop (Const (@{const_name wf}, HOLogic.mk_setT T --> @{typ bool}) $ (
                HOLogic.Collect_const T $ HOLogic.mk_case_prod (Term.abs ("t", CA1) (Term.abs ("t'", CA2) (
                  subshape_t $ Bound 1 $ Bound 0
              )))));
            in Goal.prove_sorry lthy [] [] goal (fn {context=ctxt,...} =>
              Ctr_Sugar_Tactics.unfold_thms_tac ctxt @{thms wf_def prod_in_Collect_iff} THEN
              EVERY1 [
                REPEAT_DETERM o resolve_tac ctxt [allI, impI],
                rtac ctxt subshape_induct,
                etac ctxt allE,
                etac ctxt impE,
                defer_tac,
                assume_tac ctxt,
                rtac ctxt allI,
                rtac ctxt impI,
                Goal.assume_rule_tac ctxt
              ])
            end;
          val wf_subshapess = map2 (fn CA => map2 (mk_wf_subshape CA) CAs) CAs subshapessAs

          fun mk_set_subshape_images set_ts CA ctor_t x subshape_t rename_t subshape_intro alpha_refl rename_inv_simp rename_bij =
            let
              val n = length set_ts;
              fun mk_set_subshape_image i set_t =
                let
                  val (t, _) = apfst hd (mk_Frees "t" [CA] lthy);
                  val prem = HOLogic.mk_Trueprop (HOLogic.mk_mem (t,
                    mk_image (Term.list_comb (rename_t, ffs)) $ (set_t $ x)
                  ));
                  val goal = HOLogic.mk_Trueprop (subshape_t $ t $ (ctor_t $ x));
                in prove lthy (ffs @ [t, x]) (prem_terms_ffs @ [prem]) goal (
                  mk_set_subshape_image_tac i n subshape_intro alpha_refl rename_inv_simp rename_bij
                ) end;
            in map2 mk_set_subshape_image (1 upto n) set_ts end;
          val set_subshape_imagesss = map2 (fn subshapes => fn intros =>
              @{map 10} mk_set_subshape_images rec_setss_As CAs ctorsAs xs subshapes renamesAs intros alpha_refls rename_inv_simps rename_bijs
            ) subshapessAs subshape_intross
          val set_subshapesss = map (map (map (fn thm =>
            Local_Defs.unfold0 lthy (@{thm image_id}::rename_id0s) (thm OF (
              maps (K @{thms bij_id supp_id_bound}) ffs
            ))
          ))) set_subshape_imagesss;

          fun mk_alpha_subshape supp_comp_bound alpha_t alpha_elim CA1 CA2 alpha_trans rename_comp
            mk_subshape_intros mk_alpha_bij_eqs subshape_t subshape_elim setts =
            let
              val (ys, y3) = mk_Frees "y" (replicate 2 CA1) lthy
                ||> fst o yield_singleton (mk_Frees "y") CA2;
              val (y1, y2) = `hd ys ||> hd o tl;
              val goal = [alpha_t $ y1 $ y2, subshape_t $ y3 $ y1, subshape_t $ y3 $ y2]
                |> foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop;
            in
              mk_alpha_subshape_tac fbound supp_comp_bound alpha_trans rename_comp
                mk_subshape_intros mk_alpha_bij_eqs setts alpha_elim subshape_elim raw_injects
                |> prove_no_prems lthy (ys @ [y3]) goal
            end;
          fun mk_alpha_subshapes supp_comp_bound alpha_t alpha_elim CA subshape_intros =
            let
              fun mk_subshape_intro gs (k, i) f_opts subhsape_intro = thm_instantiate_terms lthy
                (map2 (fn f_opt => fn g => SOME (case f_opt of NONE => g | SOME f =>
                  HOLogic.mk_comp (f, g))) f_opts gs) subhsape_intro OF
                (replicate (2*fbound+1) @{thm _} @ [mk_UnIN k i]);
              fun mk_subshape_intros i fs gs = @{map 3} (mk_subshape_intro gs) k_ranges
                (apply2 (replicate rec_live |> map) (replicate fbound NONE, map SOME fs)
                  |-> transpose oo map_binding_matrix) (mk_rec_lives subshape_intros)
                |> dest_rec_lives |> (fn xs => nth xs i);
              val mk_subshape_intro_funs = map mk_subshape_intros (0 upto n-1);

              fun mk_alpha_bij_eq alpha_bij_eq = Option.map (fn fs => Drule.rotate_prems ~1
                (iffD2 OF [thm_instantiate_terms lthy (map SOME fs) alpha_bij_eq]));
              fun some_bindings xs = map2 (fn b => if b then K NONE else SOME) no_bindings xs;
              fun mk_alpha_bij_eqs i fs = map2 mk_alpha_bij_eq (mk_rec_lives alpha_bij_eqs) (apply2
                (replicate rec_live |> map) (map (HOLogic.id_const o domain_type o fastype_of) fs,
                  fs) |-> transpose oo map_binding_matrix |> some_bindings) |> dest_rec_lives
                |> (fn xs => nth xs i);
              val mk_alpha_bij_eq_funs = map mk_alpha_bij_eqs (0 upto n-1);

              val alpha_transs = map (Drule.rotate_prems 1) alpha_transs;
            in
              @{map 8} (mk_alpha_subshape supp_comp_bound alpha_t alpha_elim CA) CAs alpha_transs
                rename_comps mk_subshape_intro_funs mk_alpha_bij_eq_funs
            end;
          val alpha_subshapess =
            let
              fun mk_sett sett = Drule.rotate_prems ~1 (sett RS rel_funD);
              val settsss = map (dest_rec_lives o map mk_sett o take rec_live o drop
                (2*fbound+passive)) settss;
            in
              @{map 8} mk_alpha_subshapes supp_comp_bounds alphasAs alpha_elims CAs subshape_intross
                subshapessAs subshape_elimss settsss
            end;

          val (Ps, frees_lthy) = mk_Frees "P" (map (fn CB => CB --> paramT --> HOLogic.boolT) CBs)
            frees_lthy;

          val TT_existential_induct =
            let
              val ball_rho_param = absfree (dest_Free rho) #> mk_Ball param;
              fun mk_ball_Pw P w = P $ w $ rho |> ball_rho_param;
              fun mk_prem_imp v' (w, P) set = (HOLogic.mk_mem (w, set $ v'), mk_ball_Pw P w)
                |> HOLogic.mk_imp |> list_all_free [w];
              fun mk_prem v v' sets cctor P = apply2 HOLogic.mk_Trueprop (HOLogic.mk_mem (rho,
                param), HOLogic.mk_conj (HOLogic.mk_eq (cctor $ v', cctor $ v),
                  HOLogic.mk_imp (map2 (mk_prem_imp v') (ws ~~ Ps |> mk_rec_lives) sets |> mk_conjs,
                    P $ (cctor $ v') $ rho))
                |> list_exists_free [v']) |> Logic.mk_implies |> fold_rev Logic.all [v, rho];

              val prems = @{map 5} mk_prem vs vs' rec_setss_Bs cctorsAs Ps;
              val goal = map2 (op $ o rpair rho oo curry op $) Ps ws |> mk_conjs |> ball_rho_param
                |> HOLogic.mk_Trueprop;

              val Pws = map2 mk_ball_Pw Ps ws;
              val conj_Pws = let val dummies = Term.dummy_pattern HOLogic.boolT |> replicate n;
                in map2 (fn i => fn t => nth_map i (K t) dummies |> mk_conjs) (0 upto n-1) Pws end;
              fun mk_arg_cong t w = thm_instantiate_dummy_terms lthy [NONE, NONE,
                absfree (dest_Free w) t |> SOME] arg_cong RS iffD1;
              val conj_arg_congs = map2 mk_arg_cong conj_Pws ws ~~ TT_Quotients;
              val arg_congs = map2 mk_arg_cong Pws ws |> mk_rec_lives;

              val subshape_induct_inst = thm_instantiate_terms lthy ((map2 (curry op $) TT_abss ys
                |> map2 mk_ball_Pw Ps |> map2 (absfree o dest_Free) ys) @ map2 (curry op $)
                TT_reps ws |> map SOME) subshape_induct;
              fun mk_exE mrbnf_map_AsBs assm rho x = exE OF [thm_instantiate_terms lthy (map SOME
                [rho, comb_mrbnf_term (map HOLogic.id_const As) TT_abss mrbnf_map_AsBs $ x]) assm];
              val mk_exE_funs = map mk_exE mrbnf_maps_AsBs;

              val alpha_subshapess = map2 (fn thm => mk_rec_lives o map (op OF o rpair [thm]))
                alpha_syms alpha_subshapess;
              fun mk_alpha_trans mrbnf_map_AsAs alpha_trans alpha_sym alpha_intro_id x =
                thm_instantiate_terms lthy [comb_mrbnf_term (map HOLogic.id_const As)
                  (map2 (curry HOLogic.mk_comp) TT_reps TT_abss) mrbnf_map_AsAs $ x |> SOME]
                (Drule.rotate_prems 1 alpha_trans OF [@{thm _}, alpha_sym OF [alpha_intro_id]]);
              val mk_alpha_trans_funs = @{map 4} mk_alpha_trans mrbnf_maps_AsAs alpha_transs
                alpha_syms alpha_intros_id;

              fun mk_subshape_intro_id (k, i) subhsape_intro = (subhsape_intro OF replicate fbound
                @{thms bij_id supp_id_bound} |> flat) |> Drule.rotate_prems ~1 OF [mk_UnIN k i];
              val subshape_intross_id = map (map2 mk_subshape_intro_id k_ranges o mk_rec_lives)
                subshape_intross;
            in
              mk_TT_existential_induct_tac rename_ids Quotient_rep_abss subshape_induct_inst
                conj_arg_congs arg_congs (mk_rec_lives TT_Quotients) (mk_rec_lives alpha_refls)
                raw_exhausts TT_abs_ctors mk_exE_funs cctor_defs map_comps mr_rel_maps set_maps
                Quotient_total_abs_eq_iffs mr_rel_refl_ids alpha_subshapess mk_alpha_trans_funs
                subshape_intross_id
                |> prove lthy (param :: Ps @ ws) prems goal
            end;

          val TT_fresh_induct_param =
            let
              fun mk_prem1 varsOf = [HOLogic.mk_mem (rho, param), varsOf $ rho |> mk_bound]
                |> foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop |> Logic.all rho;

              fun mk_prem_imp v (w, P) set =
                [HOLogic.mk_mem (w, set $ v), HOLogic.mk_mem (rho, param), P $ w $ rho]
                |> foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop |> fold_rev Logic.all [w, rho];
              fun mk_varsOf_imp v z set varsOf =
                [HOLogic.mk_mem (z, set $ v), HOLogic.mk_mem (z, varsOf $ rho) |> HOLogic.mk_not]
                |> foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop |> Logic.all z;
              fun mk_prem2 v bsets sets cctor P = map2 (mk_prem_imp v) (ws ~~ Ps |> mk_rec_lives)
                sets @ @{map 3} (mk_varsOf_imp v) zs bsets varsOfs @ map HOLogic.mk_Trueprop
                  [HOLogic.mk_mem (rho, param), P $ (cctor $ v) $ rho]
                |> foldr1 Logic.mk_implies |> fold_rev Logic.all [v, rho];

              val ball_rho_param = absfree (dest_Free rho) #> mk_Ball param;
              val prems = map mk_prem1 varsOfs @
                @{map 5} mk_prem2 vs bound_setss_Bs rec_setss_Bs cctorsAs Ps;
              val goal = map2 (op $ o rpair rho oo curry op $) Ps ws |> mk_conjs |> ball_rho_param
                |> HOLogic.mk_Trueprop;

              val aavoid_freshss = (map o map)
                (fn thm => Drule.rotate_prems ~1 (@{thm Int_emptyD} OF [thm])) aavoid_freshss;
              fun mk_exI aavoid_t x rho = thm_instantiate_terms lthy
                [NONE, list_comb (aavoid_t $ x, map (op $ o rpair rho) varsOfs) |> SOME] exI;
              val mk_exI_funs = map mk_exI aavoidsAs;
            in
              mk_TT_fresh_induct_param_tac TT_existential_induct mk_exI_funs alpha_aavoids
                aavoid_freshss
                |> prove lthy (param :: Ps @ ws @ varsOfs) prems goal
            end;

          val TT_fresh_induct_param_no_clash =
            let
              fun mk_prem1 varsOf = [HOLogic.mk_mem (rho, param), varsOf $ rho |> mk_bound]
                |> foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop |> Logic.all rho;

              fun mk_varsOf_imp v z set varsOf =
                [HOLogic.mk_mem (z, set $ v), HOLogic.mk_mem (z, varsOf $ rho) |> HOLogic.mk_not]
                |> foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop |> Logic.all z;
              fun mk_free_set_imp z v bset fset = [HOLogic.mk_mem (z, bset $ v),
                HOLogic.mk_mem (z, fset $ v) |> HOLogic.mk_not]
                |> foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop |> Logic.all z;
              fun mk_non_clash_imp z v bset (w, FFVars_t) set = [HOLogic.mk_mem (z, bset $ v),
                HOLogic.mk_mem (w, set $ v), HOLogic.mk_mem (z, FFVars_t $ w) |> HOLogic.mk_not]
                |> foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop |> fold_rev Logic.all [z, w];
              fun mk_imps v sets z fset bset bvec FFVars_ts varsOf = [mk_varsOf_imp v z bset varsOf,
                mk_free_set_imp z v bset fset] @ (map2 (mk_non_clash_imp z v bset)
                (ws ~~ FFVars_ts |> mk_rec_lives) sets |> filter_like bvec not);

              fun mk_prem_imp v (w, P) set =
                [HOLogic.mk_mem (w, set $ v), HOLogic.mk_mem (rho, param), P $ w $ rho]
                |> foldr1 Logic.mk_implies o map HOLogic.mk_Trueprop |> fold_rev Logic.all [w, rho];
              fun mk_prem2 v fsets bsets sets cctor P = map2 (mk_prem_imp v)
                (ws ~~ Ps |> mk_rec_lives) sets @ flat (@{map 6} (mk_imps v sets) zs fsets bsets
                  binding_matrix FFVarsssAs varsOfs) @ map HOLogic.mk_Trueprop
                  [HOLogic.mk_mem (rho, param), P $ (cctor $ v) $ rho]
                |> foldr1 Logic.mk_implies |> fold_rev Logic.all [v, rho];

              val ball_rho_param = absfree (dest_Free rho) #> mk_Ball param;
              val prems = map mk_prem1 varsOfs @
                @{map 6} mk_prem2 vs free_setss_Bs bound_setss_Bs rec_setss_Bs cctorsAs Ps;
              val goal = map2 (op $ o rpair rho oo curry op $) Ps ws |> mk_conjs |> ball_rho_param
                |> HOLogic.mk_Trueprop;

              val Sprod_t = foldr1 mk_Sigma_prod (param :: map HOLogic.mk_UNIV CBs);
              fun mk_union_t varsOf FFVars_ts = varsOf $ rho :: map2 (curry op $) FFVars_ts ws
                |> foldl1 mk_union |> fold_case_prod (rho :: ws);
              val union_ts = map2 mk_union_t varsOfs FFVarsssAs;
              fun mk_imp_t w w' P = HOLogic.mk_imp (HOLogic.mk_eq (w, w'), P $ w' $ rho)
                |> fold_case_prod (rho :: ws) |> absfree (dest_Free w');
              val imp_ts = @{map 3} mk_imp_t ws ws' Ps;
              val meta_mp_inst = meta_mp OF [@{thm _}, thm_instantiate_terms lthy
                (Sprod_t :: union_ts @ imp_ts @ ws |> map SOME) TT_fresh_induct_param];

              val UNIV_Is = map (fn w => thm_instantiate_terms lthy [SOME w] UNIV_I) (rev ws);
            in
              mk_TT_fresh_induct_param_no_clash_tac fbound n meta_mp_inst UNIV_Is
                (flat card_of_FFVars_boundss) Un_bounds (flat FFVars_cctorss)
                |> prove lthy (param :: Ps @ ws @ varsOfs) prems goal
            end;

          val TT_fresh_induct =
            let
              val Qs = mk_Frees "Q" (map (fn CB => CB --> HOLogic.boolT) CBs) frees_lthy |> fst;
              val ts = HOLogic.mk_UNIV paramT :: map (dest_Free rho |> absfree) fsets @
                map2 (fn w => fold_rev (absfree o dest_Free) [w, rho] o op $ o rpair w) ws Qs
                |> map SOME;
            in
              thm_instantiate_fixed_terms lthy ts (fsets @ Qs) TT_fresh_induct_param_no_clash
                |> full_simplify lthy
            end;
          val TT_plain_induct = (TT_fresh_induct OF
            (replicate fbound @{thm supp_id_bound[unfolded supp_id]})) |> full_simplify lthy;
        in
          (TT_existential_induct, TT_fresh_induct_param, SOME TT_fresh_induct_param_no_clash,
            SOME subshapessAs,
            SOME subshape_induct, SOME wf_subshapess, SOME set_subshape_imagesss, SOME set_subshapesss,
            TT_fresh_induct, TT_plain_induct, lthy)
        end;

    fun mk_rrename_ids rrename_t w rrename_def rename_id Quotient_abs_rep =
      let
        val goal = mk_Trueprop_eq (list_comb (rrename_t, fids) $ w, w);
      in
        mk_rrename_id_tac rrename_def rename_id Quotient_abs_rep
          |> prove_no_prems lthy ws goal
      end;
    val rrename_ids = @{map 5} mk_rrename_ids rrenamesAs ws rrename_defs rename_ids
      Quotient_abs_reps;
    val rrename_id0s = map (fn thm => @{thm meta_eq_to_obj_eq} OF [
      Local_Defs.unfold0 lthy @{thms id_def[symmetric]} (Local_Defs.abs_def_rule lthy thm)
    ]) rrename_ids;

    fun mk_rrename_comps rrename_t w rrename_def Quotient_total_abs_eq_iff alpha_refl alpha_sym alpha_trans
      alpha_bij_eq alpha_quotient_sym rename_comp =
      let
        val goal = mk_Trueprop_eq (
          list_comb (rrename_t, fgs) $ (list_comb (rrename_t, ffs) $ w),
          list_comb (rrename_t, map2 (curry HOLogic.mk_comp) fgs ffs) $ w
        );
      in
        prove lthy (ffs @ fgs @ [w]) prem_terms_ffs_fgs goal (
          mk_rrename_comp_tac rrename_def Quotient_total_abs_eq_iff alpha_refl alpha_sym alpha_trans
            alpha_bij_eq alpha_quotient_sym rename_comp
        )
      end;
    val rrename_comps = @{map 10} mk_rrename_comps rrenamesAs ws rrename_defs Quotient_total_abs_eq_iffs
      alpha_refls alpha_syms alpha_transs alpha_bij_eqs alpha_quotient_syms rename_comps;
    val rrename_comp0s = mk_rename_comp0s lthy rrename_comps rrenamesAs;

    fun mk_rrename_cong_id w rrename_t FFVars_ts FFVars_defs rrename_def Quotient_abs_rep
      Quotient_total_abs_eq_iff alpha_bij rename_id alpha_refl =
      let
        fun mk_eq f z FFVars_t = Logic.mk_implies (HOLogic.mk_mem (z, FFVars_t $ w)
          |> HOLogic.mk_Trueprop, mk_Trueprop_eq (f $ z, z)) |> Logic.all z;
        val goal = @{map 3} mk_eq ffs zs FFVars_ts @ [mk_Trueprop_eq
          (list_comb (rrename_t, ffs) $ w, w)] |> foldr1 Logic.mk_implies;
        val alpha_bij = unfold_thms lthy [rename_id, id_apply] (alpha_bij OF
          replicate (2*fbound) @{thm _} @ (replicate fbound @{thms bij_id supp_id_bound} |> flat));
      in
        mk_rrename_cong_id_tac FFVars_defs rrename_def Quotient_abs_rep Quotient_total_abs_eq_iff
          alpha_bij alpha_refl
          |> prove lthy (ffs @ ws) prem_terms_ffs goal
      end;
    val rrename_cong_ids = @{map 10} mk_rrename_cong_id ws rrenamesAs (transpose FFVarsssAs)
      (transpose FFVars_defss) rrename_defs Quotient_abs_reps Quotient_total_abs_eq_iffs alpha_bijs
      rename_ids alpha_refls;

    val rrename_bijs = @{map 3} (mk_rename_bij lthy) rrenamesAs rrename_comp0s rrename_id0s;
    val rrename_inv_simps = @{map 3} (mk_rename_inv_simp lthy) rrenamesAs rrename_comp0s rrename_id0s;

    fun mk_FFVars_rrename f w rrename_t rrename_def alpha_sym alpha_quotient_sym FVars_rename FFVars_t FFVars_def alpha_FVars =
      let
        val goal = mk_Trueprop_eq (
          FFVars_t $ (list_comb (rrename_t, ffs) $ w), mk_image f $ (FFVars_t $ w)
        );
      in
        prove lthy (ffs @ [w]) prem_terms_ffs goal (fn ctxt => fn prems =>
          Ctr_Sugar_Tactics.unfold_thms_tac ctxt [rrename_def, FFVars_def] THEN
          EVERY1 [
            rtac ctxt trans,
            rtac ctxt alpha_FVars,
            rtac ctxt alpha_sym,
            rtac ctxt alpha_quotient_sym,
            rtac ctxt FVars_rename,
            REPEAT_DETERM o resolve_tac ctxt prems
          ]
        )
      end;
    val FFVars_rrenamess = @{map 5} (fn f => @{map 9} (mk_FFVars_rrename f) ws rrenamesAs rrename_defs alpha_syms alpha_quotient_syms)
      ffs FVars_renamess FFVarsssAs FFVars_defss alpha_FVarsss

    val cctor_eq_intro_rrenames = map (fn thm => (thm RS iffD2)
      |> funpow fbound (fn thm => thm OF [exI]) OF [mk_conjIN (3*fbound + 1)]) TT_injects0;

    (* TODO: use giant map instead of x times (nth ... i) *)
    val ress = map (fn i =>
      let
        fun nth_opt xs_opt i = Option.map (fn xs => nth xs i) xs_opt
        val raw_fp_res = {
          T = nth CAs i,
          ctor = nth ctorsAs i,
          rename = nth renamesAs i,
          FVars = nth FVarsssAs i,

          inject = nth raw_injects i,
          rename_id0 = nth rename_id0s i,
          rename_id = nth rename_ids i,
          rename_comp0 = nth rename_comp0s i,
          rename_comp = nth rename_comps i,
          rename_bij = nth rename_bijs i,
          rename_inv_simp = nth rename_inv_simps i,
          FVars_ctors = nth FVars_ctorss i,
          FVars_renames = nth FVars_renamess i,
          card_of_FVars_bounds = nth card_of_FVars_boundss i,
          inner = {
            alpha = nth alphasAs i,

            exhaust = nth raw_exhausts i,
            rename_simp = nth rename_simps i,

            alpha_refl = nth alpha_refls i,
            alpha_sym = nth alpha_syms i,
            alpha_trans = nth alpha_transs i,
            alpha_bij = nth alpha_bijs i,
            alpha_bij_eq = nth alpha_bij_eqs i,
            alpha_FVarss = nth alpha_FVarsss i,
            alpha_intro = nth alpha_intros i,
            alpha_elim = nth alpha_elims i,

            subshapes = nth_opt subshapess_opt i,
            wf_subshapes = nth_opt wf_subshapess_opt i,
            set_subshapess = nth_opt set_subshapesss_opt i,
            set_subshape_imagess = nth_opt set_subshape_imagesss_opt i,
            subshape_induct = TT_subshape_induct_opt
          }
        } : raw_result fp_result_T;
        val quotient_fp_res = {
          T = nth CBs i,
          ctor = nth cctorsAs i,
          rename = nth rrenamesAs i,
          FVars = nth FFVarsssAs i,

          inject = nth TT_injects0 i,
          rename_id0 = nth rrename_id0s i,
          rename_id = nth rrename_ids i,
          rename_comp0 = nth rrename_comp0s i,
          rename_comp = nth rrename_comps i,
          rename_bij = nth rrename_bijs i,
          rename_inv_simp = nth rrename_inv_simps i,
          FVars_ctors = nth FFVars_cctorss i,
          FVars_renames = nth FFVars_rrenamess i,
          card_of_FVars_bounds = nth card_of_FFVars_boundss i,
          inner = {
            abs = nth TT_abss i,
            rep = nth TT_reps i,

            ctor_def = nth cctor_defs i,
            rename_def = nth rrename_defs i,
            FVars_defs = nth FFVars_defss i,

            alpha_quotient_sym = nth alpha_quotient_syms i,
            total_abs_eq_iff = nth Quotient_total_abs_eq_iffs i,
            abs_rep = nth Quotient_abs_reps i,
            rep_abs = nth Quotient_rep_abss i,
            abs_ctor = nth TT_abs_ctors i,

            rename_ctor = nth rrename_cctors i
          }
        } : quotient_result fp_result_T;
      in {
        fp = fp,
        binding_relation = binding_relation,
        bound_vars = fAs,
        raw_fp = raw_fp_res,
        quotient_fp = quotient_fp_res,
        pre_mrbnf = nth mrbnfs i
      } : fp_result end
    ) (0 upto n - 1);

    val lthy = register_fp_results ress lthy

    val notes =
      [("rename_simps", rename_simps),
       ("rename_id0s", rename_id0s),
       ("rename_ids", rename_ids),
       ("rename_comp0s", rename_comp0s),
       ("rename_comps", rename_comps),
       ("rename_bijs", rename_bijs),
       ("rename_inv_simps", rename_inv_simps),
       ("FVars_ctors", flat FVars_ctorss),
       ("FVars_rename_less", flat FVars_rename_less),
       ("FVars_renames", flat FVars_renamess),
       ("card_of_FVars_bounds", flat card_of_FVars_boundss),
       ("alpha_refls", alpha_refls),
       ("alpha_bijs", alpha_bijs),
       ("alpha_bij_eqs", alpha_bij_eqs),
       ("alpha_bij_eq_invs", alpha_bij_eq_invs),
       ("alpha_FVarss", flat alpha_FVarsss),
       ("alpha_syms", alpha_syms),
       ("alpha_transs", alpha_transs),
       ("card_of_FVarsB_bounds", flat card_of_FVarsB_boundss),
       ("refresh_sets", refresh_sets),
       ("refreshs", refreshs),
       ("avoid_freshs", flat avoid_freshss),
       ("alpha_avoids", alpha_avoids),
       ("equivp_alphas", equivp_alphas),
       ("TT_Quotients", TT_Quotients),
       ("TT_alpha_quotient_syms", alpha_quotient_syms),
       ("TT_Quotient_total_abs_eq_iffs", Quotient_total_abs_eq_iffs),
       ("TT_Quotient_abs_reps", Quotient_abs_reps),
       ("TT_Quotient_rep_abss", Quotient_rep_abss),
       ("TT_abs_ctors", TT_abs_ctors),
       ("TT_nchotomys", TT_nchotomys),
       ("rrename_cctors", rrename_cctors),
       ("card_of_FFVars_bounds", flat card_of_FFVars_boundss),
       ("FFVars_cctors", flat FFVars_cctorss),
       ("FFVars_intros", flat FFVars_intross),
       ("FFVars_elims", flat FFVars_elimss),
       ("FFVars_inducts", FFVars_inducts),
       ("FFVars_rrenames", flat FFVars_rrenamess),
       ("TT_injects0", TT_injects0),
       ("aavoid_freshs", flat aavoid_freshss),
       ("alpha_aavoids", alpha_aavoids),
       ("TT_fresh_nchotomys", TT_fresh_nchotomys),
       ("TT_fresh_cases", TT_fresh_cases),
       ("TT_existential_co_induct", [TT_existential_co_induct]),
       ("TT_fresh_co_induct_param", [TT_fresh_co_induct_param]),
       ("TT_fresh_co_induct", [TT_fresh_co_induct]),
       ("TT_plain_co_induct", [TT_plain_co_induct]),
       ("rrename_id0s", rrename_id0s),
       ("rrename_ids", rrename_ids),
       ("rrename_comps", rrename_comps),
       ("rrename_comp0s", rrename_comp0s),
       ("rrename_cong_ids", rrename_cong_ids),
       ("cctor_eq_intro_rrenames", cctor_eq_intro_rrenames)
      ] @ (the_default [] (
        Option.map (single o pair "TT_fresh_induct_param_no_clash" o single)
        TT_fresh_induct_param_no_clash_opt
      )) @ (the_default [] (
        Option.map (single o pair "TT_subshape_induct" o single)
        TT_subshape_induct_opt
      )) @ (the_default [] (
        Option.map (single o pair "wf_subshapes" o flat)
        wf_subshapess_opt
      )) @ (the_default [] (
        Option.map (single o pair "set_subshape_images" o flat o flat)
        set_subshape_imagesss_opt
      ))  @ (the_default [] (
        Option.map (single o pair "set_subshapes" o flat o flat)
        set_subshapesss_opt
      )) |> (map (fn (thmN, thms) =>
        ((Binding.qualify true (hd names) (Binding.name thmN), []), [(thms, [])])
      ));

    val (noted, lthy') = Local_Theory.notes notes lthy
  in
    (ress, lthy')
  end;

end;
