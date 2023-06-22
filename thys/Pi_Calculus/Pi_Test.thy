theory Pi_Test
  imports "../../thys/MRBNF_Recursor"
begin

ML \<open>
val ctors = [
  (("Zero", (NONE : mixfix option)), []),
  (("Sum", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Par", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Bang", NONE), [@{typ 'rec}]),
  (("Match", NONE), [@{typ 'var}, @{typ 'var}, @{typ 'rec}]),
  (("Out", NONE), [@{typ 'var}, @{typ 'var}, @{typ 'rec}]),
  (("Inp", NONE), [@{typ 'var}, @{typ 'bvar}, @{typ 'brec}]),
  (("Res", NONE), [@{typ 'bvar}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "term"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

ML \<open>
Multithreading.parallel_proofs := 4
\<close>

local_setup \<open>fn lthy =>
let
  val name1 = "commit_internal"
  val name2 = "commit"
  val T1 = @{typ "'var term"}
  val T2 = @{typ "'var * 'var * 'var term +'var * 'var * 'var term +  'bvar * 'brec"}
  val Xs = map dest_TFree []
  val resBs = map dest_TFree [@{typ 'var}, @{typ 'bvar}, @{typ 'brec}, @{typ 'rec}]
  val rel = [[0]]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify1 = Binding.prefix_name (name1 ^ "_pre_")
  val qualify2 = Binding.prefix_name (name2 ^ "_pre_")

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf1, tys1), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify1 flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] T1
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val ((mrbnf2, tys2), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify2 flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] T2
    (accum, lthy);

  val (tys, _, (mrbnfs as [mrbnf1, mrbnf2], (accum, lthy))) =
      MRBNF_Comp.normalize_mrbnfs (K I) [] (map (map dest_TFree) [snd tys1, snd tys2])
      [] (K (resBs @ Xs)) NONE [mrbnf1, mrbnf2] (accum, lthy);

  (* Step 2: Seal the pre-MRBNF with a typedef *)
  val ((mrbnf1, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name1 ^ "_pre")) true (fst tys1) [] mrbnf1 lthy
  val ((mrbnf2, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name2 ^ "_pre")) true (fst tys2) [] mrbnf2 lthy

  (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
  val (bnf1, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf1 lthy
  val (bnf2, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf2 lthy

  (* Step 4: Create fixpoint of pre-MRBNF *)
  val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [
    ((name1, mrbnf1), 1), ((name2, mrbnf2), 1)
  ] rel lthy;
in lthy end
\<close>
print_theorems

definition Finp :: "'a::{var_commit_pre,var_commit_internal_pre} \<Rightarrow> 'a \<Rightarrow> 'a term \<Rightarrow> 'a commit" where
  "Finp x y t \<equiv> commit_ctor (Abs_commit_pre (Inl (x, y, t)))"
definition Fout :: "'a::{var_commit_pre,var_commit_internal_pre} \<Rightarrow> 'a \<Rightarrow> 'a term \<Rightarrow> 'a commit" where
  "Fout x y t \<equiv> commit_ctor (Abs_commit_pre (Inr (Inl (x, y, t))))"
definition Bout :: "'a::{var_commit_pre,var_commit_internal_pre} \<Rightarrow> 'a term \<Rightarrow> 'a commit" where
  "Bout x t \<equiv> commit_ctor (Abs_commit_pre (Inr (Inr (x, commit_internal_ctor (Abs_commit_internal_pre t)))))"

lemma FFVars_commit_simps[simp]:
  "FFVars_commit (Finp x y t) = {x, y} \<union> FFVars_term t"
  "FFVars_commit (Fout x y t) = {x, y} \<union> FFVars_term t"
  "FFVars_commit (Bout x t) = FFVars_term t - {x}"
  apply (unfold Bout_def Finp_def Fout_def)
  apply (rule trans)
     apply (rule commit_internal.FFVars_cctors)
    defer
    apply (rule trans, rule commit_internal.FFVars_cctors)
    defer
    apply (rule trans, rule commit_internal.FFVars_cctors)
  apply (unfold set1_commit_pre_def comp_def Abs_commit_pre_inverse[OF UNIV_I] map_prod_simp
    UN_empty UN_empty2 prod_set_simps set3_commit_pre_def cSup_singleton Un_empty_left Un_empty_right
    Sup_empty set2_commit_pre_def set4_commit_pre_def UN_single map_sum.simps sum_set_simps
  )
  apply (rule arg_cong2[OF _ refl, of _ _ minus])
  apply (rule trans)
   apply (rule commit_internal.FFVars_cctors)
  apply (unfold set1_commit_internal_pre_def comp_def Abs_commit_internal_pre_inverse[OF UNIV_I] map_prod_simp prod_set_simps
    UN_empty cSup_singleton Un_empty_left Un_empty_right set3_commit_internal_pre_def empty_Diff
    set4_commit_internal_pre_def
  )
    apply auto
  done


end