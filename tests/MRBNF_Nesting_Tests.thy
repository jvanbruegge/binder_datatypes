theory MRBNF_Nesting_Tests
  imports "../thys/MRBNF_Recursor" "../DALList"
begin

datatype \<tau> = Base | Arrow \<tau> \<tau> (infixr "(\<rightarrow>)" 50)

lemma disjointI: "(\<And>x. x \<in> A \<Longrightarrow> x \<notin> B) \<Longrightarrow> A \<inter> B = {}"
  by blast
lemma notin_empty_eq_True: "x \<notin> {} = True"
  by simp
lemma Int_empty_single: "{x} \<inter> A = {} \<longleftrightarrow> x \<notin> A"
  by blast

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Lam", NONE), [@{typ 'bvar}, @{typ \<tau>}, @{typ 'brec}]),
  (("Let", NONE), [@{typ "('bvar, \<tau> \<times> 'rec) dallist"}, @{typ 'brec}]),
  (("Var2", NONE), [@{typ 'tvar}]),
  (("Lam2", NONE), [@{typ 'tbvar}, @{typ \<tau>}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "term"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'tvar}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'tbvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[1], [1]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst}
}

val info_ref = Unsynchronized.ref (NONE : MRBNF_Comp.absT_info option);
val vvsubst_res_ref = Unsynchronized.ref (NONE : MRBNF_VVSubst.vvsubst_result option);
\<close>

local_setup \<open>fn lthy =>
let
  val fp_pre_T = BNF_FP_Util.mk_sumprodT_balanced (map snd (#ctors spec));
  val _ = @{print} fp_pre_T

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
    val ((rec_mrbnf, vvsubst_res), lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint (#map_b spec) I (hd res) lthy;
    val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (#quotient_fp (hd res))))) rec_mrbnf lthy;
    val _ = (info_ref := SOME info);
    val _ = (vvsubst_res_ref := SOME vvsubst_res);
  in lthy end
\<close>

ML_file \<open>../Tools/mrbnf_sugar.ML\<close>

ML \<open>
Multithreading.parallel_proofs := 0
\<close>

declare [[ML_print_depth=10000]]

local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec (the (!vvsubst_res_ref)) (the (!info_ref)) lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

declare [[names_short]]
thm
  term.strong_induct
  term.fresh_induct
  term.induct

thm term.set
thm term.map
thm term.distinct

end