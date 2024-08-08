theory Composition
  imports "Binders.MRBNF_Composition"
begin

declare [[mrbnf_internals]]

(* TODO: Show proofs as apply script *)
ML \<open>
val ctor_T1_Ts = [
  [@{typ 'var}],
  [@{typ unit}],
  [@{typ 'tyvar}],
  [@{typ 'rec}, @{typ 'rec2}],
  [@{typ 'bvar}, @{typ 'brec}],
  [@{typ 'btyvar}, @{typ 'brec}],
  [@{typ 'a}]
]
val ctor_T2_Ts = [
  [@{typ 'var}],
  [@{typ 'tyvar}],
  [@{typ 'rec}, @{typ 'rec2}],
  [@{typ 'bvar}, @{typ "'brec list"}],
  [@{typ 'btyvar}, @{typ 'brec2}],
  [@{typ 'b}, @{typ 'rec}]
]
\<close>

ML \<open>
val T1 = BNF_FP_Util.mk_sumprodT_balanced ctor_T1_Ts
val T2 = BNF_FP_Util.mk_sumprodT_balanced ctor_T2_Ts
val name1 = "T1";
val name2 = "T2";
val rel = [[1,3], [1]];
Multithreading.parallel_proofs := 4
\<close>

declare [[quick_and_dirty]]
declare [[ML_print_depth=1000]]
declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val Xs = map dest_TFree [@{typ 'a}, @{typ 'b}]
  val resBs = map dest_TFree [@{typ 'var}, @{typ 'tyvar}, @{typ 'bvar}, @{typ 'btyvar}, @{typ 'rec}, @{typ 'brec}, @{typ 'rec2}, @{typ 'brec2}]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify1 = Binding.prefix_name (name1 ^ "_pre_")
  val qualify2 = Binding.prefix_name (name2 ^ "_pre_")
  val accum = (MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds)

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf1, tys1), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify1 flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
      (dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var),
      (dest_TFree @{typ 'a}, MRBNF_Def.Free_Var)
    ] T1
    (accum, lthy)
  val _ = @{print} "comp1"
  val ((mrbnf2, tys2), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify2 flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
      (dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var),
      (dest_TFree @{typ 'a}, MRBNF_Def.Free_Var)
    ] T2
    (accum, lthy);
  val _ = @{print} "comp2"

  val nvars = length rel;
  val (tys, _, (mrbnfs as [mrbnf1, mrbnf2], (accum, lthy))) =
      MRBNF_Comp.normalize_mrbnfs (K I) [] (map (map dest_TFree) [snd tys1, snd tys2])
      [] [] (K (take nvars resBs @ Xs @ drop nvars resBs)) NONE [mrbnf1, mrbnf2] (accum, lthy)
  val _ = @{print} "normalize"
  val _ = @{print} tys

  (* Step 2: Seal the pre-MRBNF with a typedef *)
  val ((mrbnf1, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name1 ^ "_pre")) true (fst tys1) [] mrbnf1 lthy
  val _ = @{print} "seal1"
  val ((mrbnf2, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name2 ^ "_pre")) true (fst tys2) [] mrbnf2 lthy
  val _ = @{print} "seal2"

  (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
  val (bnf1, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf1 lthy
  val (bnf2, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf2 lthy
  val _ = @{print} "register"
in lthy end
\<close>
print_theorems
print_bnfs

declare [[quick_and_dirty=false]]

lemmas infinite_UNIV = cinfinite_imp_infinite[OF T1_pre.UNIV_cinfinite]

end