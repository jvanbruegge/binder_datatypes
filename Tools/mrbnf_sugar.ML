signature MRBNF_SUGAR =
sig

type spec = {
  fp_b: binding,
  vars: ((string * sort) * MRBNF_Def.var_type) list,
  rec_vars: int,
  binding_rel: int list list,
  ctors: ((string * mixfix option) * typ list) list,
  map_b: binding
};

val create_binder_datatype : spec -> local_theory -> local_theory

end

structure MRBNF_Sugar : MRBNF_SUGAR =
struct

open BNF_Util
open BNF_FP_Util
open MRBNF_Def

type spec = {
  fp_b: binding,
  vars: ((string * sort) * MRBNF_Def.var_type) list,
  rec_vars: int,
  binding_rel: int list list,
  ctors: ((string * mixfix option) * typ list) list,
  map_b: binding
};

fun add_nesting_mrbnf_names Us =
  let
    fun add (Type (s, Ts)) ss =
        let val (needs, ss') = fold_map add Ts ss in
          if exists I needs then (true, insert (op =) s ss') else (false, ss')
        end
      | add T ss = (member (op =) Us T, ss);
  in snd oo add end;

fun nesting_mrbnfs ctxt ctr_Tsss Us =
  map_filter (mrbnf_of ctxt) (fold (fold (fold (add_nesting_mrbnf_names Us))) ctr_Tsss []);

fun create_binder_datatype spec lthy =
  let
    val fp_pre_T = foldr1 mk_sumT (map (foldr1 HOLogic.mk_prodT o snd) (#ctors spec))

    val (resBs, Xs) = fold_rev (
      fn (x, Free_Var) => (fn (a, b) => (x::a, b))
       | (x, _) => (fn (a, b) => (a, x::b))
    ) (#vars spec) ([], []);
    fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;

    val name = Binding.name_of (#fp_b spec);
    val pre_name = name ^ "_pre_" ^ name;
    val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline
      (Binding.prefix_name pre_name) flatten_tyargs Xs [] (#vars spec) fp_pre_T ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy);

    val ((mrbnf, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name pre_name) true (fst tys) [] mrbnf lthy;
    val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy
    val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [((name, mrbnf), #rec_vars spec)] (#binding_rel spec) lthy;
    (*val (rec_mrbnf, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint (#map_b spec) I (hd res) lthy;*)
    (*val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (#quotient_fp (hd res))))) rec_mrbnf lthy;*)

    val quotient_ctor = #ctor (#quotient_fp (hd res));
    val replace = map (TFree o fst) (#vars spec) ~~ snd (dest_Type (domain_type (fastype_of quotient_ctor)));
    val pre_repT = Term.typ_subst_atomic replace fp_pre_T;
    val n = length replace;
    val abs =
      let val (s, _) = dest_Const (#abs info)
      in Const (s, pre_repT --> domain_type (fastype_of quotient_ctor)) end;

    val (_, lthy) = Local_Theory.begin_nested lthy;
    val (ctors, (_, _, _, lthy)) = fold_map (fn (((name, _), Ts)) => fn (i, T, ts, lthy) =>
      let
        val Ts' = map (Term.typ_subst_atomic replace) Ts;
        val (xs, _) = mk_Frees Name.uu Ts' lthy;
        val (now, later, RT) = if i = n then ([], [], T) else
          let val (LT, RT) = BNF_FP_Util.dest_sumT T;
          in ([Inl_const LT RT], [Inr_const LT RT], RT) end;
        val rhs = fold_rev Term.absfree (map dest_Free xs) (
          quotient_ctor $ (abs $ fold_rev (curry (op$)) (ts @ now) (
            HOLogic.mk_tuple xs
          ))
        );
        val (ctor, lthy) = MRBNF_Recursor.mk_def_t true Binding.empty I name 0 rhs lthy
      in (ctor, (i+1, RT, ts @ later, lthy)) end
    ) (#ctors spec) (1, pre_repT, [], lthy);

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;
    val vars' = rev (map TVar (Term.add_tvars (Morphism.term phi (fst (hd ctors))) []));
    val vars = rev (map TFree (Term.add_tfreesT (range_type (fastype_of quotient_ctor)) []));
    fun morph (t, thm) = (
      Term.subst_atomic_types (vars' ~~ vars) (Morphism.term phi t),
      Morphism.thm phi thm
    );
    val ctors = map morph ctors;

    val _ = @{print} ctors

    (*val fp_nesting_mrbnfs = nesting_mrbnfs lthy [map snd (#ctors spec)] (take (#rec_vars spec) (
      map_filter (fn (x, Live_Var) => SOME (TFree x) | _ => NONE) (#vars spec)
    ));*)


  in lthy end;

end