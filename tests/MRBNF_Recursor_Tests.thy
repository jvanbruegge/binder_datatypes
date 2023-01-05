theory MRBNF_Recursor_Tests
  imports "../thys/MRBNF_Recursor"
begin


(*ML_file \<open>../Tools/mrbnf_recursor_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_recursor.ML\<close>

ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>

(* Test 1: One free variable in the fixpoint, bound in first recursive component *)
local_setup \<open>fn lthy =>
let
  val name = "test1"
  val T = @{typ "'var + unit + 'rec * 'rec + 'bvar * 'brec"}
  val Xs = map dest_TFree [@{typ 'bvar}, @{typ 'brec}, @{typ 'rec}]
  val resBs = map dest_TFree [@{typ 'var}]
  val rel = [[0]]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (name ^ "_pre_")

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] T
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)

  (* Step 2: Seal the pre-MRBNF with a typedef *)
  val ((mrbnf, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name ^ "_pre")) true (fst tys) [] mrbnf lthy

  (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
  val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy

  (* Step 4: Create fixpoint of pre-MRBNF *)
  val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [((name, mrbnf), 2)] rel lthy;

  (* Step 5: Create recursor and create fixpoint as MRBNF *)
  val (rec_mrbnf, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint @{binding vvsubst} I (hd res) lthy;

  (* Step 6: Register fixpoint MRBNF *)
  val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (#quotient_fp (hd res))))) rec_mrbnf lthy;
in lthy end
\<close>
print_theorems

(* Test 2: One free variable in the fixpoint, bound in second recursive component *)
local_setup \<open>fn lthy =>
let
  val name = "test2"
  val T = @{typ "'var + unit + 'rec * 'rec + 'bvar * 'brec"}
  val Xs = map dest_TFree [@{typ 'bvar}, @{typ 'rec}, @{typ 'brec}]
  val resBs = map dest_TFree [@{typ 'var}]
  val rel = [[1]]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (name ^ "_pre_")

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] T
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)

  (* Step 2: Seal the pre-MRBNF with a typedef *)
  val ((mrbnf, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name ^ "_pre")) true (fst tys) [] mrbnf lthy

  (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
  val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy

  (* Step 4: Create fixpoint of pre-MRBNF *)
  val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [((name, mrbnf), 2)] rel lthy;

  (* Step 5: Create recursor and create fixpoint as MRBNF *)
  val (rec_mrbnf, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint (Binding.prefix_name (name ^ "_") @{binding vvsubst}) I (hd res) lthy;

  (* Step 6: Register fixpoint MRBNF *)
  val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (#quotient_fp (hd res))))) rec_mrbnf lthy;
in lthy end
\<close>*)

declare [[ML_print_depth=100000]]

ML \<open>
Multithreading.parallel_proofs := 0
\<close>

(* Test 3: Two free variable in the fixpoint *)
local_setup \<open>fn lthy =>
let
  val name = "test3"
  val T = @{typ "'var + unit + 'tyvar + 'rec * 'rec + 'bvar * 'brec + 'btyvar * 'brec"}
  val Xs = map dest_TFree [@{typ 'bvar}, @{typ 'btyvar}, @{typ 'brec}, @{typ 'rec}]
  val resBs = map dest_TFree [@{typ 'var}, @{typ 'tyvar}]
  val rel = [[0], [0]]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (name ^ "_pre_")

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
      (dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var)
    ] T
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)

  (* Step 2: Seal the pre-MRBNF with a typedef *)
  val ((mrbnf, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name ^ "_pre")) true (fst tys) [] mrbnf lthy

  (* Step 3: Register the sealed MRBNF as BNF in its live variables *)
  val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy

  (*(* Step 4: Create fixpoint of pre-MRBNF *)
  val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [((name, mrbnf), 2)] rel lthy;*)
in lthy end
\<close>

ML_file \<open>../Tools/mrbnf_fp_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_fp_def_sugar.ML\<close>
ML_file \<open>../Tools/mrbnf_fp.ML\<close>

(*ML_file \<open>../Tools/mrbnf_recursor_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_recursor.ML\<close>

ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>*)

local_setup \<open>fn lthy =>
let
  val mrbnf = the (MRBNF_Def.mrbnf_of lthy "MRBNF_Recursor_Tests.test3_pre");
  val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [(("test3", mrbnf), 2)] [[0], [0]] lthy;
  (*val (rec_mrbnf, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint (Binding.prefix_name ("test3" ^ "_") @{binding vvsubst}) I (hd res) lthy;*)
in lthy end\<close>

end