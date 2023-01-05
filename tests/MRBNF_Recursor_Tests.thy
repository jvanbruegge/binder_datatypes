theory MRBNF_Recursor_Tests
  imports "../thys/MRBNF_Recursor" "HOL-Eisbach.Eisbach"
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

(*
binder_datatype ('a, 'b) test3 =
  Var 'a | Arrow | Data 'b | App test3 test3 | Abs x::'a t::test3 binds x in t
*)
declare [[mrbnf_internals,bnf_internals]]
(* Test 3: One free variable in the fixpoint, but also one passive variable *)
local_setup \<open>fn lthy =>
let
  val name = "test3"
  val T = @{typ "'var + unit + 'passive + 'rec * 'rec + 'bvar * 'brec"}
  val Xs = map dest_TFree [@{typ 'bvar}, @{typ 'brec}, @{typ 'rec}]
  val resBs = map dest_TFree [@{typ 'var}, @{typ 'passive}]
  val rel = [[0]]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (name ^ "_pre_")

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] T
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

ML_file \<open>../Tools/mrbnf_recursor_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_recursor.ML\<close>

ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>

ML \<open>
Multithreading.parallel_proofs := 0;
\<close>


local_setup \<open>fn lthy =>
let
  val mrbnf = the (MRBNF_Def.mrbnf_of lthy "MRBNF_Recursor_Tests.test3_pre");
  val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [(("test3", mrbnf), 2)] [[0]] lthy;
  val (rec_mrbnf, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint (Binding.prefix_name ("test3" ^ "_") @{binding vvsubst}) I (hd res) lthy;
in lthy end\<close>
  
print_theorems

type_synonym ('a, 'b, 'c) U = "('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'c) test3"

definition CCTOR2 :: "('a::var_test3_pre, 'b, 'a, ('a, 'b) test3 \<times> ('a ssfun \<Rightarrow> ('a, 'b, 'c) U), ('a, 'b) test3 \<times> ('a ssfun \<Rightarrow> ('a, 'b, 'c) U)) test3_pre \<Rightarrow> 'a ssfun \<Rightarrow> ('a, 'b, 'c) U" where
  "CCTOR2 x f1 \<equiv> \<lambda>f2. test3_ctor (map_test3_pre (Rep_ssfun f1) f2 id ((\<lambda>R. R f1 f2) \<circ> snd) ((\<lambda>R. R f1 f2) \<circ> snd) x)"

definition Umap :: "('a::var_test3_pre \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) test3 \<Rightarrow> ('a, 'b, 'c) U \<Rightarrow> ('a, 'b, 'c) U" where
  "Umap f _ u \<equiv> \<lambda>g. rrename_test3 f (u g)"

lemmas compSS_comp = fun_cong[OF compSS_comp0[OF cinfinite_imp_infinite[OF test3_pre.UNIV_cinfinite]], unfolded comp_def]
lemma Umap_Uctor:
  fixes f::"'a::var_test3_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "Umap f (test3_ctor (map_test3_pre id id id fst fst y)) (CCTOR2 y p)  = CCTOR2 (map_test3_pre f id f
    (\<lambda>(t, pt). (rrename_test3 f t, \<lambda>p. Umap f t (pt (compSS (inv f) p))))
    (\<lambda>(t, pt). (rrename_test3 f t, \<lambda>p. Umap f t (pt (compSS (inv f) p)))) y)
  (compSS f p)"
  apply (unfold Umap_def CCTOR2_def)
  apply (rule ext)
  apply (rule trans[rotated])
   apply (rule sym)
   apply (rule arg_cong[of _ _ test3_ctor])
   apply (rule test3_pre.map_comp)
        apply (rule assms iffD1[OF mem_Collect_eq Rep_ssfun] supp_id_bound bij_id)+
  apply (rule trans)
   apply (rule tmp.rrename_simp)
    apply (rule assms)+
  apply (rule trans)
   apply (rule arg_cong[of _ _ test3_ctor])
  apply (rule test3_pre.map_comp)
        apply (rule assms iffD1[OF mem_Collect_eq Rep_ssfun] supp_id_bound bij_id)+
  apply (unfold id_o o_id)
  apply (unfold comp_def case_prod_beta snd_conv)
  apply (unfold comp_def compSS_comp[OF bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms] assms]
    inv_simp1[OF assms(1)] id_def[symmetric] compSS_id
    compSS_rep_eq[OF cinfinite_imp_infinite[OF test3_pre.UNIV_cinfinite] assms]
  )
  apply (unfold id_def)
  apply (rule refl)
  done

type_synonym 'a U2 = "'a set"

definition CCTOR3 :: "('a::var_test3_pre, 'b, 'a, ('a, 'b) test3 \<times> (unit \<Rightarrow> 'b U2), ('a, 'b) test3 \<times> (unit \<Rightarrow> 'b U2)) test3_pre \<Rightarrow> unit \<Rightarrow> 'b U2" where
  "CCTOR3 x _ \<equiv> set2_test3_pre x \<union> \<Union>((\<lambda>pt. (snd pt) ()) ` set4_test3_pre x) \<union> \<Union>((\<lambda>pt. snd pt ()) ` set5_test3_pre x)"

definition Umap2 :: "('a::var_test3_pre \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) test3 \<Rightarrow> 'b U2 \<Rightarrow> 'b U2" where
  "Umap2 _ _ u \<equiv> u"

lemma Umap_Uctor2:
  fixes f::"'a::var_test3_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "Umap2 f (test3_ctor (map_test3_pre id id id fst fst y)) (CCTOR3 y p)  = CCTOR3 (map_test3_pre f id f
    (\<lambda>(t, pt). (rrename_test3 f t, \<lambda>p. Umap2 f t (pt ())))
    (\<lambda>(t, pt). (rrename_test3 f t, \<lambda>p. Umap2 f t (pt ()))) y)
  p"
  apply (unfold Umap2_def CCTOR3_def image_id image_comp comp_def case_prod_beta snd_conv
    test3_pre.set_map[OF assms(2) assms]
  )
  apply (rule refl)
  done

type_synonym ('a, 'b, 'c) U3 = "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"

definition CCTOR4 :: "('a::var_test3_pre, 'b, 'a, ('a, 'b) test3 \<times> (('a, 'c) test3 \<Rightarrow> ('a, 'b, 'c) U3), ('a, 'b) test3 \<times> (('a, 'c) test3 \<Rightarrow>('a, 'b, 'c) U3)) test3_pre \<Rightarrow> ('a, 'c) test3 \<Rightarrow> ('a, 'b, 'c) U3" where
  "CCTOR4 x t \<equiv> \<lambda>R. \<forall>y. test3_ctor y = t \<longrightarrow> mr_rel_test3_pre id R id
      (\<lambda>a b. snd a b R) (\<lambda>a b. snd a b R) x y"
definition CCTOR5 :: "('a::var_test3_pre, 'b, 'a, ('a, 'b) test3 \<times> (('a, 'c) test3 \<Rightarrow> ('a, 'b, 'c) U3), ('a, 'b) test3 \<times> (('a, 'c) test3 \<Rightarrow>('a, 'b, 'c) U3)) test3_pre \<Rightarrow> ('a, 'c) test3 \<Rightarrow> ('a, 'b, 'c) U3" where
  "CCTOR5 x t \<equiv> \<lambda>R. \<exists>y. test3_ctor y = t \<and> mr_rel_test3_pre id R id (\<lambda>a b. snd a b R) (\<lambda>a b. snd a b R) x y"
definition Umap3 :: "('a::var_test3_pre \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) test3 \<Rightarrow> ('a, 'b, 'c) U3 \<Rightarrow> ('a, 'b, 'c) U3" where
  "Umap3 f _ x \<equiv> x"

lemma Umap_Uctor3:
  fixes f::"'a::var_test3_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "Umap3 f (test3_ctor (map_test3_pre id id id fst fst y)) (CCTOR4 y p) = CCTOR4 (map_test3_pre f id f
    (\<lambda>(t, pt). (rrename_test3 f t, \<lambda>p. Umap3 f t (pt (rrename_test3 (inv f) p))))
    (\<lambda>(t, pt). (rrename_test3 f t, \<lambda>p. Umap3 f t (pt (rrename_test3 (inv f) p)))) y)
  (rrename_test3 f p)"
  apply (unfold Umap3_def CCTOR4_def)
  apply (rule ext)
  apply (rule iffI)
   apply (rule allI impI)+
   apply (drule sym[THEN iffD2[OF bij_imp_inv'[OF tmp.rrename_bij[OF assms]]]])
   apply (unfold tmp.rrename_inv_simp[OF assms] tmp.rrename_simp[OF bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]])
   apply (erule allE)
   apply (erule impE)
    apply assumption
   apply hypsubst_thin
   apply (drule iffD2[OF test3_pre.mr_rel_flip, rotated -1])
       apply (rule bij_id supp_id_bound)+
   apply (unfold inv_id)
   apply (drule iffD1[OF test3_pre.mr_rel_map(1), rotated -1])
         apply (rule supp_inv_bound assms bij_imp_bij_inv supp_id_bound bij_id)+
   apply (unfold id_o o_id Grp_UNIV_id eq_OO)
   apply (drule iffD2[OF test3_pre.mr_rel_flip, rotated -1])
       apply (rule bij_imp_bij_inv supp_inv_bound assms)+
   apply (unfold inv_inv_eq[OF assms(1)] conversep_conversep)
   apply (rule iffD2[OF test3_pre.mr_rel_map(1)])
         apply (rule assms supp_id_bound bij_id)+
   apply (unfold id_o converse_relcompp conversep_conversep relcompp_conversep_Grp Grp_UNIV_id eq_OO)[1]
   apply (rule test3_pre.mr_rel_mono_strong0[rotated -6])
              apply assumption
  apply (rule ballI impI refl | assumption | (
      (unfold Grp_UNIV_def OO_def case_prod_beta)[1],
        rule exI,
        rule conjI,
        rule refl,
        unfold snd_conv,
        assumption
      ))+
        apply (rule assms)+
  apply (rule allI impI)+
  apply (erule allE)
  apply hypsubst_thin
  apply (unfold tmp.rrename_simp[OF assms])
  apply (erule impE)
   apply (rule refl)
  apply (drule iffD1[OF test3_pre.mr_rel_map(1), rotated -1])
        apply (rule assms bij_id supp_id_bound)+
  apply (unfold id_o Grp_UNIV_id eq_OO)
  apply (drule iffD2[OF test3_pre.mr_rel_flip, rotated -1])
      apply (rule assms)+
  apply (drule iffD1[OF test3_pre.mr_rel_map(1), rotated -1])
        apply (rule assms supp_inv_bound bij_imp_bij_inv)+
  apply (unfold Grp_UNIV_id eq_OO inv_o_simp1[OF assms(1)])
  apply (drule iffD2[OF test3_pre.mr_rel_flip, rotated -1])
      apply (rule supp_id_bound bij_id)+
  apply (unfold inv_id converse_relcompp conversep_conversep relcompp_conversep_Grp case_prod_beta)
  apply (unfold conversep_def snd_conv tmp.rrename_comp[OF assms bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]]
    inv_o_simp1[OF assms(1)] tmp.rrename_id
  )
  apply assumption
  done

lemma Umap3_id0: "Umap3 id t = id"
  apply (unfold Umap3_def id_def)
  apply (rule refl)
  done

lemma Umap3_comp0:
  fixes f g::"'a::var_test3_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "Umap3 (f \<circ> g) t = Umap3 f t \<circ> Umap3 g t"
  apply (unfold Umap3_def comp_def)
  apply (rule refl)
  done

thm tmp.FFVars_rrenames

local_setup \<open>fn lthy =>
let
  fun rtac ctxt = resolve_tac ctxt o single
  val model_tacs = {
    small_avoiding_sets = [fn ctxt => resolve_tac ctxt @{thms emp_bound} 1],
    Umap_id0 = fn ctxt => resolve_tac ctxt @{thms Umap3_id0} 1,
    Umap_comp0 = fn ctxt => resolve_tac ctxt @{thms Umap3_comp0} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Umap_cong_ids = [fn ctxt => BNF_Tactics.unfold_thms_tac ctxt @{thms Umap3_def} THEN rtac ctxt refl 1],
    UFVars_Umap = [fn ctxt => BNF_Tactics.unfold_thms_tac ctxt @{thms image_empty} THEN rtac ctxt refl 1],
    Umap_Uctor = fn ctxt => EVERY1 [rtac ctxt @{thm Umap_Uctor3}, REPEAT_DETERM o assume_tac ctxt],
    UFVars_subsets = [fn ctxt => rtac ctxt @{thm empty_subsetI} 1]
  } : (Proof.context -> tactic) MRBNF_Recursor.model_axioms;

  val params = {
    P = @{typ "('a::var_test3_pre, 'c) test3"},
    PFVarss = [@{term "FFVars_test3 :: ('a::var_test3_pre, 'c) test3 \<Rightarrow> _"}],
    Pmap = @{term "rrename_test3 :: _ \<Rightarrow> _ \<Rightarrow> ('a::var_test3_pre, 'c) test3"},
    axioms = {
      Pmap_id0 = fn ctxt => EVERY1 (map (rtac ctxt) @{thms ext trans tmp.rrename_id id_apply[symmetric]}),
      Pmap_comp0 = fn ctxt => EVERY1 [
        rtac ctxt ext,
        rtac ctxt trans,
        rtac ctxt (@{thm tmp.rrename_comp} RS sym),
        REPEAT_DETERM o assume_tac ctxt,
        rtac ctxt @{thm comp_apply[symmetric]}
      ],
      Pmap_cong_ids = [fn ctxt => EVERY1 [
        rtac ctxt @{thm tmp.rrename_cong_id},
        REPEAT_DETERM o assume_tac ctxt,
        Goal.assume_rule_tac ctxt
      ]],
      PFVars_Pmaps = [fn ctxt => EVERY1 [
        resolve_tac ctxt @{thms tmp.FFVars_rrenames},
        REPEAT_DETERM o assume_tac ctxt
      ]],
      small_PFVarss = [fn ctxt => resolve_tac ctxt @{thms tmp.FFVars_bound_UNIV} 1]
    }
  } : (Proof.context -> tactic) MRBNF_Recursor.parameter;

  val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of lthy "MRBNF_Recursor_Tests.test3");
  val model = {
    U = @{typ "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"},
    vars = [@{typ "'a::var_test3_pre"}, @{typ 'b}],
    extra_vars = [@{typ 'c}],
    fp_result = fp_res,
    UFVars = [@{term "\<lambda>(t::('a::var_test3_pre, 'b) test3) (d::('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool). {} :: 'a set"}],
    Umap = @{term Umap3},
    Uctor = @{term CCTOR4},
    avoiding_sets = [@{term "{} :: 'a::var_test3_pre set"}],
    parameters = params,
    axioms = model_tacs
  } : (Proof.context -> tactic) MRBNF_Recursor.model;
  val (res, lthy) = MRBNF_Recursor.create_binding_recursor (Binding.suffix_name "_rel") model (Binding.name "test3_rel") lthy;
  val notes = [
    ("rel_ctor", [#rec_Uctor res]),
    ("rel_swap", [#rec_swap res])
  ] |> (map (fn (thmN, thms) =>
      ((Binding.qualify true "tmp" (Binding.name thmN), []), [(thms, [])])
      ));
  val (_, lthy) = Local_Theory.notes notes lthy;
in lthy end
\<close>

print_theorems

definition test3_rel :: "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a::var_test3_pre, 'b) test3 \<Rightarrow> ('a, 'c) test3 \<Rightarrow> bool" where
  "test3_rel R x y \<equiv> ff0_rel x y R"

thm mp[OF spec[OF spec[OF tmp.fresh_induct_param[of UNIV
      "\<lambda>(x, y). FFVars_test3 x \<union> FFVars_test3 y"
      "\<lambda>t \<rho>. \<forall>y. \<rho> = (t, y) \<longrightarrow> (test3_rel R OO test3_rel S) t y \<longrightarrow> test3_rel (R OO S) t y",
      unfolded ball_UNIV
      ]]]]
    
method rel_ctor_helper_tac uses IHs noclash_def = (
    (unfold Un_empty_right)?,
    rule iffD2[OF disjoint_iff],
    (rule allI impI)+,
    drule IHs,
    ((unfold Un_iff de_Morgan_disj)[1])?,
    (erule conjE)+,
    assumption,
    (unfold noclash_def,
    rule iffD2[OF disjoint_iff],
    (rule allI impI)+,
    drule IHs,
    unfold tmp.FFVars_ctors Un_iff de_Morgan_disj,
    (erule conjE)+,
    ((rule conjI)?, assumption)+)?
  )

thm tmp.fresh_cases
thm noclash_test3_rel_def
thm tmp.rel_ctor

lemma fresh_cases:
  assumes "|A::'a::var_test3_pre set| <o |UNIV::'a set|"
  shows "(\<And>x. w = test3_ctor x \<Longrightarrow> noclash_test3_rel x \<Longrightarrow> set3_test3_pre x \<inter> A = {} \<Longrightarrow> Q) \<Longrightarrow> Q"
  apply (unfold atomize_imp atomize_all)
  apply (rule mp[OF spec[OF tmp.fresh_induct_param[of UNIV "\<lambda>x. FFVars_test3 x \<union> A" "\<lambda>w \<rho>. w = \<rho> \<longrightarrow> (\<forall>x. w = test3_ctor x \<longrightarrow> noclash_test3_rel x \<longrightarrow> set3_test3_pre x \<inter> A = {} \<longrightarrow> Q) \<longrightarrow> Q", unfolded ball_UNIV]]])
    apply (rule test3_pre.Un_bound)
     apply (rule tmp.FFVars_bound_UNIV)
    apply (rule assms)
    apply (rule impI)+
    apply (erule allE)
    apply (erule impE)
     apply (rule refl)
   apply (erule impE)
  apply hypsubst
    apply (unfold noclash_test3_rel_def tmp.FFVars_ctors Un_iff de_Morgan_disj)[1]
  subgoal premises IH for v x
    apply (rule iffD2[OF disjoint_iff])
    apply (rule allI impI)+
    apply (drule IH)
    apply (erule conjE)+
    apply (unfold Un_iff de_Morgan_disj)
    apply ((rule conjI)?, assumption)+
    done
   apply (erule impE)
    apply (rule iffD2[OF disjoint_iff])
  subgoal premises IH
    apply (rule allI impI)+
    apply (drule IH)
    apply (unfold Un_iff de_Morgan_disj)
    apply (erule conjE)+
    apply assumption
    done
   apply assumption
  apply (rule refl)
  done

lemma le_rel_OO: "test3_rel R OO test3_rel S \<le> test3_rel (R OO S)"
  apply (rule predicate2I)
  apply (drule iffD1[OF relcompp_apply])
  apply (erule exE conjE)+
  apply (unfold atomize_imp)
  subgoal for x y
    apply (rule
        mp[OF spec[OF spec[OF spec[OF tmp.fresh_induct_param[of UNIV
                "\<lambda>(x, y, z). FFVars_test3 x \<union> FFVars_test3 y \<union> FFVars_test3 z"
                "\<lambda>t \<rho>. \<forall>y z. \<rho> = (t, y, z) \<longrightarrow> test3_rel R t z \<longrightarrow> test3_rel S z y \<longrightarrow> test3_rel (R OO S) t y",
                unfolded ball_UNIV
                ]]]]]
        )
    subgoal for x
      apply (unfold case_prod_beta prod.case)
      apply (rule test3_pre.Un_bound)+
       apply (rule tmp.FFVars_bound_UNIV)+
      done
     defer
     apply (rule refl)
    apply (rule allI impI)+
    apply hypsubst_thin
    apply (unfold prod.case test3_rel_def Un_iff de_Morgan_disj)
    subgoal premises IHs for v \<rho> t' t''
      apply (rule iffD2[OF fun_cong[OF tmp.rel_ctor]])
      apply (rel_ctor_helper_tac IHs: IHs noclash_def: noclash_test3_rel_def)
      apply (unfold CCTOR4_def)
      apply (rule allI impI)+
      apply hypsubst
      apply (rule iffD2[OF test3_pre.mr_rel_map(1)])
            apply (rule supp_id_bound bij_id)+
      apply (unfold Grp_UNIV_id eq_OO)
      apply (insert IHs(5,6))
      apply (drule iffD1[OF fun_cong[OF tmp.rel_ctor], rotated -1])
        apply (rel_ctor_helper_tac IHs: IHs noclash_def: noclash_test3_rel_def)
      apply (rule fresh_cases[of _ t''])
      apply (rule tmp.FFVars_bound_UNIV)
       apply hypsubst
           apply (drule iffD1[OF fun_cong[OF tmp.rel_ctor], rotated -1])
         apply (unfold Un_empty_right)
        apply assumption+
      apply (unfold CCTOR4_def)
      apply (erule allE, erule impE, rule refl)+
      apply (drule iffD1[OF test3_pre.mr_rel_map(1), rotated -1])
            apply (rule supp_id_bound bij_id)+
      apply (drule iffD1[OF test3_pre.mr_rel_map(1), rotated -1])
            apply (rule supp_id_bound bij_id)+
      apply (unfold id_o Grp_UNIV_id eq_OO)
      subgoal for z y
        apply (rotate_tac -2)
        apply (drule relcomppI[of _ v y _ z])
         apply assumption
        apply (drule iffD2[OF fun_cong[OF fun_cong[OF test3_pre.mr_rel_OO]], rotated -1])
              apply (rule supp_id_bound bij_id)+
        apply (unfold id_o)
        apply (rule test3_pre.mr_rel_mono_strong0[rotated -6])
                   apply assumption
                  apply ((rule ballI impI)+, (rule refl | assumption))+
        apply (
            (rule ballI impI)+,
            (unfold OO_def Grp_UNIV_def)[1],
            (erule exE conjE)+,
            hypsubst,
            (unfold snd_conv)[1],
            drule IHs,
            rule UNIV_I,
            (erule allE)+,
            erule impE, rule refl,
            erule impE, assumption,
            erule impE, assumption,
            rule exI, rule conjI, rule refl,
            (unfold snd_conv OO_def)[1],
            assumption
        )+
             apply (rule supp_id_bound bij_id)+
        done
      done
    done
  done

lemma set1_test3: "set1_test3 (test3_ctor x) = set2_test3_pre x \<union> \<Union>(set1_test3 ` set4_test3_pre x) \<union> \<Union>(set1_test3 ` set5_test3_pre x)"
  sorry

lemma imsupp_same2: "x \<notin> imsupp f \<Longrightarrow> x = f b \<Longrightarrow> x = b"
  unfolding imsupp_def supp_def by auto

definition pick :: "('a::var_test3_pre \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a, 'b) test3 \<times> ('a, 'c) test3 \<Rightarrow> ('a, 'b \<times> 'c) test3" where
  "pick f R xy \<equiv> SOME z. set1_test3 z \<subseteq> {(xa, x). R xa x} \<and> test3_vvsubst id fst z = fst xy \<and> test3_vvsubst f snd z = snd xy"

definition pick_rev :: "('a::var_test3_pre \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a, 'b \<times> 'c) test3 \<Rightarrow> ('a, 'b) test3 \<times> ('a, 'c) test3" where
  "pick_rev f R x \<equiv> SOME z. undefined"

lemma FFVars_pick:
  fixes f::"'a::var_test3_pre \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|" "x \<notin> imsupp f"
    and "A \<subseteq> {(z5, y5). \<exists>z. set1_test3 z \<subseteq> {(xa, x). R xa x} \<and> test3_vvsubst id fst z = z5 \<and> test3_vvsubst f snd z = y5}"
  shows "x \<notin> \<Union>(FFVars_test3 ` snd ` A) \<union> \<Union>(FFVars_test3 ` fst ` A) \<Longrightarrow> x \<notin> \<Union>(FFVars_test3 ` pick f R ` A)"
  apply (erule contrapos_nn)
  apply (unfold pick_def)
  apply (erule UN_E)
  apply (erule imageE)
  apply hypsubst
  apply (rule UnCI)
  apply (unfold image_comp)
  apply (rule UN_I)
   apply assumption
  apply (unfold comp_def)
  apply (drule set_mp[OF assms(3)])
  apply (unfold mem_Collect_eq case_prod_beta)
  apply (drule someI_ex)
  apply (erule conjE)+
  apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
   apply (rule arg_cong[of _ _ FFVars_test3])
   apply (rule sym)
   apply assumption
  apply (unfold tmp.FFVars_vvsubsts[OF assms(1)])
  apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"], rotated])
   apply (rule imageI)
   apply assumption
  apply (rule sym)
  apply (rule not_in_imsupp_same)
  apply (rule assms)
  done

lemma CCTOR_eq: "CCTOR4 x = CCTOR5 x" sorry

lemmas id_prems = supp_id_bound bij_id supp_id_bound
lemma in_rel:
  fixes f::"'a::var_test3_pre \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|"
  shows "test3_rel R (test3_vvsubst f id x) y =
    (\<exists>z. set1_test3 z \<subseteq> {(x, y). R x y} \<and> test3_vvsubst id fst z = x \<and> test3_vvsubst f snd z = y)"
  apply (unfold test3_rel_def)
  apply (rule mp[OF spec[OF spec[OF tmp.fresh_induct_param[of UNIV, unfolded ball_UNIV],
      of "\<lambda>(x, y). imsupp f \<union> FFVars_test3 x \<union> FFVars_test3 (test3_vvsubst f id x) \<union> FFVars_test3 y"
        "\<lambda>x \<rho>. \<forall>y. \<rho> = (x, y) \<longrightarrow> ff0_rel (test3_vvsubst f id x) y R = (\<exists>z. set1_test3 z \<subseteq> {(x, y). R x y} \<and> test3_vvsubst id fst z = x \<and> test3_vvsubst f snd z = y)"
  ]]])
   defer
    apply (rule allI impI)+
    apply hypsubst
  apply (unfold prod.case)
  subgoal premises IHs for v \<rho> y
    apply (rule trans)
     apply (rule arg_cong3[OF _ refl refl, of _ _ ff0_rel]) (* TODO: mk_arg_cong *)
     apply (rule tmp.vvsubst_ctor)
       apply (rule assms)
      apply (rel_ctor_helper_tac IHs: IHs noclash_def: noclash_test3_def)
    apply (rule trans)
     apply (rule fun_cong[OF tmp.rel_ctor])
    apply (unfold test3_pre.set_map[OF assms bij_id supp_id_bound] image_id noclash_test3_rel_def)
      apply (rel_ctor_helper_tac IHs: IHs)
     apply (rule iffD2[OF disjoint_iff])
     apply (rule allI impI)+
     apply (drule IHs)
     apply (unfold Un_iff de_Morgan_disj)[1]
     apply (erule conjE)+
     apply (rule conjI)
      apply (unfold tmp.FFVars_vvsubsts[OF assms] tmp.FFVars_ctors Un_iff de_Morgan_disj image_Un)[1]
      apply (erule conjE)+
      apply assumption
     apply (rotate_tac 1)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated -1])
      apply (rule arg_cong[of _ _ FFVars_test3])
      apply (rule tmp.vvsubst_ctor)
        apply (rule assms)
       apply (rel_ctor_helper_tac IHs: IHs noclash_def: noclash_test3_def)
     apply (erule conjE)+
     apply (unfold test3_pre.set_map[OF assms bij_id supp_id_bound])
     apply assumption
    apply (unfold test3_pre.map_comp[OF assms bij_id supp_id_bound supp_id_bound bij_id supp_id_bound]
        id_o
        )




    apply (unfold CCTOR4_def)
    apply (rule fresh_cases[OF emp_bound, of y])
    apply hypsubst_thin
 

    apply (rule iffI)
     apply (erule allE)
     apply (erule impE)
      apply (rule refl)
     apply (drule iffD1[OF test3_pre.mr_rel_map(1), rotated -1])
           apply (rule assms supp_id_bound bij_id)+
     apply (unfold id_o Grp_UNIV_id eq_OO)
    subgoal for x
      apply (unfold comp_def OO_def Grp_UNIV_def)
      apply (drule test3_pre.mr_rel_mono_strong0[rotated -6])
                 apply (rule ballI)
                 apply (rule refl)
                apply (rule ballI)+
                apply (rule imp_refl)
               apply (rule ballI refl)+
              apply (rule impI)
              apply (erule exE)
              apply (erule conjE)
              apply hypsubst
              apply (unfold snd_conv)
              apply (drule IHs)
               apply (rule UNIV_I)
              apply (erule allE)
              apply (erule impE)
               apply (rule refl)
              apply (drule iffD1)
               apply assumption
              apply (rotate_tac -1)
              apply assumption

    (* REPEAT *)
      apply (rule ballI refl)+
              apply (rule impI)
              apply (erule exE)
              apply (erule conjE)
              apply hypsubst
              apply (unfold snd_conv)
              apply (drule IHs)
               apply (rule UNIV_I)
              apply (erule allE)
              apply (erule impE)
               apply (rule refl)
              apply (drule iffD1)
               apply assumption
              apply (rotate_tac -1)
             apply assumption
            apply (rule assms bij_id supp_id_bound)+


      apply (drule iffD1[OF test3_pre.mr_in_rel, rotated -1])
         apply (rule assms bij_id supp_id_bound)+
      apply (erule exE conjE)+
      subgoal for za
        apply (rule exI[of _ "test3_ctor (map_test3_pre id id id (pick f R) (pick f R) za)"])
        apply (rule conjI)
         apply (unfold set1_test3 test3_pre.set_map[OF supp_id_bound  bij_id supp_id_bound] image_id Un_subset_iff UN_subset_iff)
         apply (rule conjI)+
           apply assumption

(* TODO: repeat *)
          apply (rule ballI)
          apply (erule imageE)
          apply hypsubst
          apply (drule set_mp[rotated])
           apply assumption
          apply (unfold pick_def mem_Collect_eq case_prod_beta)[1]
          apply (rule someI2_ex)
        apply assumption
          apply (erule conjE)+
          apply assumption

apply (rule ballI)
          apply (erule imageE)
          apply hypsubst
          apply (frule set_mp[rotated])
           apply assumption
          apply (unfold pick_def mem_Collect_eq case_prod_beta)[1]
         apply (rule someI2_ex)
        apply assumption
          apply (erule conjE)+
         apply assumption


        apply hypsubst
apply (frule arg_cong[of _ _ "set3_test3_pre"])
          apply (frule arg_cong[of _ _ "set1_test3_pre"])
        apply (frule arg_cong[of _ _ "set5_test3_pre"])
          apply (unfold test3_pre.set_map[OF supp_id_bound bij_id supp_id_bound] image_id)
        apply (rule conjI)
         apply (rule trans)
          apply (rule tmp.vvsubst_ctor)
        apply (rule supp_id_bound)
           apply (unfold imsupp_id)
           apply (rule Int_empty_right)

(* TODO: make more efficient (is used again later) *)
          apply (unfold noclash_test3_rel_def noclash_test3_def
            test3_pre.set_map[OF assms bij_id supp_id_bound] image_id
            test3_pre.set_map[OF supp_id_bound bij_id supp_id_bound]
        )[1]

          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI)
          apply (rule impI)
  apply (drule iffD1[OF disjoint_iff, rotated -1])
          apply (erule allE)
          apply (erule impE)
        apply assumption
          apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
        apply (rule sym)
           apply assumption
          apply (drule IHs)
          apply (unfold tmp.FFVars_ctors test3_pre.set_map[OF supp_id_bound bij_id supp_id_bound] image_id Un_iff de_Morgan_disj)
          apply (erule conjE)+
          apply (rule conjI)+
           apply simp
        apply hypsubst
          apply (unfold test3_pre.set_map[OF supp_id_bound bij_id supp_id_bound] image_id)
          apply (rule FFVars_pick)
             apply (rule assms)
            apply assumption
           apply assumption
          apply (unfold Un_iff de_Morgan_disj)
          apply (rule conjI)
           apply assumption
          apply assumption

         apply (unfold test3_pre.map_comp[OF id_prems id_prems] id_o o_id)
         apply (rule arg_cong[of _ _ test3_ctor])
         apply (rule test3_pre.map_cong)
                    apply (rule supp_id_bound bij_id refl)+
          apply (drule set_mp[rotated])
           apply assumption
          apply (unfold mem_Collect_eq case_prod_beta)
          apply (erule exE)
          apply (unfold comp_def pick_def)[1]
          apply (rule someI2)
           apply (unfold case_prod_beta)[1]
           apply assumption
          apply (erule conjE)+
          apply assumption
        (* repeated *)
      apply (drule set_mp[rotated])
           apply assumption
          apply (unfold mem_Collect_eq case_prod_beta)
          apply (erule exE)
          apply (unfold comp_def pick_def)[1]
          apply (rule someI2)
           apply (unfold case_prod_beta)[1]
           apply assumption
          apply (erule conjE)+
         apply assumption


        apply (rule trans)
         apply (rule tmp.vvsubst_ctor)
           apply (rule assms)
          apply (unfold test3_pre.set_map[OF id_prems] image_id)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
           apply (rule sym)
           apply assumption
          apply (drule IHs)
          apply (unfold Un_iff de_Morgan_disj)[1]
          apply (erule conjE)+
        apply assumption
        
(* noclash tac repeated here *)
 apply (unfold noclash_test3_rel_def noclash_test3_def
            test3_pre.set_map[OF assms bij_id supp_id_bound] image_id
            test3_pre.set_map[OF supp_id_bound bij_id supp_id_bound]
        )[1]

          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI)
          apply (rule impI)
  apply (drule iffD1[OF disjoint_iff, rotated -1])
          apply (erule allE)
          apply (erule impE)
        apply assumption
          apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
        apply (rule sym)
           apply assumption
          apply (drule IHs)
          apply (unfold tmp.FFVars_ctors test3_pre.set_map[OF supp_id_bound bij_id supp_id_bound] image_id Un_iff de_Morgan_disj)
          apply (erule conjE)+
          apply (rule conjI)+
           apply simp
        apply hypsubst
          apply (unfold test3_pre.set_map[OF supp_id_bound bij_id supp_id_bound] image_id)
          apply (rule FFVars_pick)
             apply (rule assms)
           apply assumption
        apply (unfold case_prod_beta)
           apply assumption
          apply (unfold Un_iff de_Morgan_disj)
          apply (rule conjI)
           apply assumption
         apply assumption

         apply (unfold test3_pre.map_comp[OF id_prems id_prems] test3_pre.map_comp[OF id_prems assms(1) bij_id supp_id_bound] id_o o_id)
         apply (rule arg_cong[of _ _ test3_ctor])
         apply (rule test3_pre.map_cong)
                    apply (rule assms supp_id_bound bij_id refl)+
          apply (drule set_mp[rotated])
           apply assumption
          apply (unfold mem_Collect_eq case_prod_beta)
          apply (erule exE)
          apply (unfold comp_def pick_def)[1]
          apply (rule someI2)
           apply (unfold case_prod_beta)[1]
           apply assumption
          apply (erule conjE)+
          apply assumption
        (* repeated *)
      apply (drule set_mp[rotated])
           apply assumption
          apply (unfold mem_Collect_eq case_prod_beta)
          apply (erule exE)
          apply (unfold comp_def pick_def)[1]
          apply (rule someI2)
           apply (unfold case_prod_beta)[1]
           apply assumption
          apply (erule conjE)+
        apply assumption
        done
      done

  (* other direction *)
    apply (rule allI impI)+

    apply (rule iffD2[OF test3_pre.mr_rel_map(1)])
          apply (rule assms bij_id supp_id_bound)+
    apply (unfold id_o Grp_UNIV_id eq_OO)

    apply (rule test3_pre.mr_rel_mono_strong0[rotated -5])
               apply (rule ballI)
               apply (rule refl)
              apply (rule ballI)+
              apply (rule imp_refl)
             apply (rule ballI)
             apply (rule refl)
            apply (rule ballI)+
            apply (unfold Grp_UNIV_def OO_def comp_def)[1]
            apply (rule impI)
            apply (rule exI)
            apply (rule conjI)
             apply (rule refl)
            apply (unfold snd_conv)
            apply (drule IHs)
             apply (rule UNIV_I)
            apply (rotate_tac -1)
            apply (erule allE)
            apply (rotate_tac -1)
            apply (erule impE)
             apply (rule refl)
            apply (rule iffD1)
             apply (rule sym)
             apply (rotate_tac -1)
             apply assumption
            apply assumption

           apply (rule ballI impI)+
           apply (unfold Grp_UNIV_def OO_def comp_def)[1]
           apply (rule exI)
           apply (rule conjI)
            apply (rule refl)
           apply (unfold snd_conv)
           apply (tactic \<open>dmatch_tac @{context} @{thms IHs} 1\<close>)
            apply (rule UNIV_I)
           apply (tactic \<open>ematch_tac @{context} @{thms allE} 1\<close>)
           apply (tactic \<open>ematch_tac @{context} @{thms impE} 1\<close>)
            apply (rule refl)
           apply (rule iffD1)
            apply (rule sym)
            apply (rotate_tac -1)
            apply assumption
           apply assumption
          apply (rule assms supp_id_bound bij_id)+

    apply (erule exE conjE)+
    apply (rotate_tac -1)
    apply (drule trans)
     apply (rule sym)
     apply assumption

    apply (rule iffD2[OF test3_pre.mr_in_rel])
       apply (rule assms supp_id_bound bij_id)+

    subgoal for x' y z
      apply (rule fresh_cases[of _ z])
       apply (rule iffD2[OF imsupp_supp_bound[OF cinfinite_imp_infinite[OF test3_pre.UNIV_cinfinite]] assms])
      apply hypsubst_thin


      apply (rotate_tac 4)
      apply (drule trans[rotated])
       apply (rule sym)
       apply (rule tmp.vvsubst_ctor)
         apply (rule supp_id_bound)
        apply (unfold imsupp_id noclash_test3_rel_def noclash_test3_def[symmetric])
        apply (rule Int_empty_right)
       apply assumption
      apply (drule trans[rotated])
       apply (rule sym)
       apply (rule tmp.vvsubst_ctor)
         apply (rule assms)
        apply assumption
       apply assumption

      apply (rotate_tac 2)
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (erule thin_rl)

      apply (unfold set1_test3 tmp.inject)
      apply (erule exE conjE)+
      apply (unfold test3_pre.set_map[OF id_prems] image_id test3_pre.map_comp[OF id_prems supp_id_bound]
        id_o o_id tmp.vvsubst_rrename[symmetric]
        test3_pre.set_map[OF assms bij_id supp_id_bound]
        test3_pre.map_comp[OF assms bij_id supp_id_bound supp_id_bound]
        ext[of "test3_vvsubst _ _", OF tmp.vvsubst_comp[OF supp_id_bound], symmetric]
        ext[of "test3_vvsubst _ _", OF tmp.vvsubst_comp[OF assms], symmetric]
      )
      apply hypsubst_thin
      subgoal for z' g1 g2
        apply (rule exI[of _ "map_test3_pre id id g1 (BNF_Def.convol (test3_vvsubst g1 fst) (test3_vvsubst (g2 \<circ> f) snd)) (BNF_Def.convol (test3_vvsubst id fst) (test3_vvsubst f snd)) z'"])
        apply (unfold test3_pre.set_map[OF supp_id_bound] image_id
          test3_pre.map_comp[OF supp_id_bound _ _ id_prems] id_o o_id fst_convol snd_convol
          test3_pre.map_comp[OF supp_id_bound _ _ assms bij_id supp_id_bound]
        )


        apply (unfold Un_subset_iff)
        apply (erule conjE)+
        apply (rule conjI)
         apply assumption
        apply (rule conjI)
         apply (rule subsetI)
         apply (unfold mem_Collect_eq case_prod_beta)
         apply (erule imageE)
         apply hypsubst
        apply (unfold fst_convol' snd_convol')

      thm IHs
      term "map_test3_pre id id g1 (BNF_Def.convol (test3_vvsubst id fst) (test3_vvsubst id snd)) (BNF_Def.convol (test3_vvsubst id fst) (test3_vvsubst id snd))"

     (* subgoal for k
      apply (rule exI[of _ "map_test3_pre id id id (pick_rev f R) (pick_rev f R) k"])
      apply (unfold test3_pre.set_map[OF id_prems] image_id
        test3_pre.map_comp[OF id_prems id_prems] id_o o_id set1_test3 Un_subset_iff
      )
        apply (erule conjE)+
        apply (rule conjI)
         apply assumption
        apply (rule conjI)+
         apply (rule subsetI)
         apply (unfold mem_Collect_eq case_prod_beta UN_subset_iff)
        apply (erule ballE)*)


      oops


lemma in_imsupp: "f a \<noteq> a \<Longrightarrow> a \<in> imsupp f"
  unfolding imsupp_def supp_def by blast

lemma imsupp_Int_same: "imsupp g \<inter> imsupp f = {} \<Longrightarrow> a \<in> imsupp f \<Longrightarrow> g (f a) = f a"
  unfolding imsupp_def supp_def by auto

lemma ex_avoiding_bij:
  fixes f :: "'a \<Rightarrow> 'a" and I D A :: "'a set"
  assumes  "|supp f| <o |UNIV :: 'a set|" "bij f" "infinite (UNIV :: 'a set)"
    "|I| <o |UNIV :: 'a set|" "id_on I f"
    "|D| <o |UNIV :: 'a set|" "D \<inter> A = {}" "|A| <o |UNIV :: 'a set|"
  shows "\<exists>(g::'a \<Rightarrow> 'a). bij g \<and> |supp g| <o |UNIV::'a set| \<and> imsupp g \<inter> A = {} \<and>
    (\<forall>a. a \<in> (imsupp f - A) \<union> D \<and> f a \<notin> A \<longrightarrow> g a = f a) \<and> id_on I g"
  apply (rule exI[of _ "avoiding_bij f I D A"])
  apply (rule conjI avoiding_bij assms)+
  done

lemma in_rel:
  fixes f::"'a::var_test3_pre \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|"
  shows "test3_rel R (test3_vvsubst f id x) y =
    (\<exists>z. set1_test3 z \<subseteq> {(x, y). R x y} \<and> test3_vvsubst id fst z = x \<and> test3_vvsubst f snd z = y)"
  apply (unfold test3_rel_def)
  apply (rule mp[OF spec[OF spec[OF tmp.fresh_induct_param[of UNIV, unfolded ball_UNIV],
      of "\<lambda>(x, y). imsupp f \<union> FFVars_test3 x \<union> FFVars_test3 (test3_vvsubst f id x) \<union> FFVars_test3 y"
        "\<lambda>x \<rho>. \<forall>y. \<rho> = (x, y) \<longrightarrow> ff0_rel (test3_vvsubst f id x) y R = (\<exists>z. set1_test3 z \<subseteq> {(x, y). R x y} \<and> test3_vvsubst id fst z = x \<and> test3_vvsubst f snd z = y)"
  ]]])
   defer
    apply (rule allI impI)+
    apply hypsubst
  apply (unfold prod.case)
  subgoal premises IHs for v \<rho> y
    apply (rule trans)
     apply (rule arg_cong3[OF _ refl refl, of _ _ ff0_rel]) (* TODO: mk_arg_cong *)
     apply (rule tmp.vvsubst_ctor)
       apply (rule assms)
      apply (rel_ctor_helper_tac IHs: IHs noclash_def: noclash_test3_def)
    apply (rule trans)
     apply (rule fun_cong[OF tmp.rel_ctor])
    apply (unfold test3_pre.set_map[OF assms bij_id supp_id_bound] image_id noclash_test3_rel_def)
      apply (rel_ctor_helper_tac IHs: IHs)
     apply (rule iffD2[OF disjoint_iff])
     apply (rule allI impI)+
     apply (drule IHs)
     apply (unfold Un_iff de_Morgan_disj)[1]
     apply (erule conjE)+
     apply (rule conjI)
      apply (unfold tmp.FFVars_vvsubsts[OF assms] tmp.FFVars_ctors Un_iff de_Morgan_disj image_Un)[1]
      apply (erule conjE)+
      apply assumption
     apply (rotate_tac 1)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated -1])
      apply (rule arg_cong[of _ _ FFVars_test3])
      apply (rule tmp.vvsubst_ctor)
        apply (rule assms)
       apply (rel_ctor_helper_tac IHs: IHs noclash_def: noclash_test3_def)
     apply (erule conjE)+
     apply (unfold test3_pre.set_map[OF assms bij_id supp_id_bound])
     apply assumption
    apply (unfold test3_pre.map_comp[OF assms bij_id supp_id_bound supp_id_bound bij_id supp_id_bound]
        id_o
        )

    apply (unfold CCTOR_eq)
    apply (unfold CCTOR5_def)
    apply (rule iffI)
     apply (erule exE conjE)+


 apply (drule iffD1[OF test3_pre.mr_rel_map(1), rotated -1])
           apply (rule assms supp_id_bound bij_id)+
  apply (unfold id_o Grp_UNIV_id eq_OO)

   subgoal for x
      apply (unfold comp_def OO_def Grp_UNIV_def)
      apply (drule test3_pre.mr_rel_mono_strong0[rotated -6])
                 apply (rule ballI)
                 apply (rule refl)
                apply (rule ballI)+
                apply (rule imp_refl)
               apply (rule ballI refl)+
              apply (rule impI)
              apply (erule exE)
              apply (erule conjE)
              apply hypsubst
              apply (unfold snd_conv)
              apply (drule IHs)
               apply (rule UNIV_I)
              apply (erule allE)
              apply (erule impE)
               apply (rule refl)
              apply (drule iffD1)
               apply assumption
              apply (rotate_tac -1)
              apply assumption

    (* REPEAT *)
      apply (rule ballI refl)+
              apply (rule impI)
              apply (erule exE)
              apply (erule conjE)
              apply hypsubst
              apply (unfold snd_conv)
              apply (drule IHs)
               apply (rule UNIV_I)
              apply (erule allE)
              apply (erule impE)
               apply (rule refl)
              apply (drule iffD1)
               apply assumption
              apply (rotate_tac -1)
             apply assumption
            apply (rule assms bij_id supp_id_bound)+
 apply (drule iffD1[OF test3_pre.mr_in_rel, rotated -1])
        apply (rule assms bij_id supp_id_bound)+
     apply (erule exE conjE)+
subgoal for za
        apply (rule exI[of _ "test3_ctor (map_test3_pre id id id (pick f R) (pick f R) za)"])
        apply (rule conjI)
         apply (unfold set1_test3 test3_pre.set_map[OF supp_id_bound  bij_id supp_id_bound] image_id Un_subset_iff UN_subset_iff)
         apply (rule conjI)+
     apply assumption
apply (rule ballI)
          apply (erule imageE)
          apply hypsubst
          apply (drule set_mp[rotated])
           apply assumption
          apply (unfold pick_def mem_Collect_eq case_prod_beta)[1]
          apply (rule someI2_ex)
        apply assumption
          apply (erule conjE)+
    apply assumption

apply (rule ballI)
          apply (erule imageE)
          apply hypsubst
          apply (frule set_mp[rotated])
           apply assumption
          apply (unfold pick_def mem_Collect_eq case_prod_beta)[1]
         apply (rule someI2_ex)
        apply assumption
          apply (erule conjE)+
         apply assumption

apply hypsubst
apply (frule arg_cong[of _ _ "set3_test3_pre"])
          apply (frule arg_cong[of _ _ "set1_test3_pre"])
  apply (frule arg_cong[of _ _ "set5_test3_pre"])

  apply (subst (asm) test3_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id)

  apply (rule conjI)
apply (rule trans)
          apply (rule tmp.vvsubst_ctor)
        apply (rule supp_id_bound)
           apply (unfold imsupp_id)
     apply (rule Int_empty_right)
    apply (unfold noclash_test3_def)[1]
    apply (subst test3_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id noclash_test3_rel_def)[1]

apply (rule iffD2[OF disjoint_iff])
          apply (rule allI)
    apply (rule impI)

    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule sym)
     apply assumption
    apply (drule IHs)
    apply (unfold Un_iff de_Morgan_disj tmp.FFVars_ctors)[1]
    apply (erule conjE)+

    apply (rule conjI)
     apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<notin>)"]])
      apply (rule sym)
      apply assumption
     apply assumption
    apply hypsubst
    apply (subst (asm) test3_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id)
    apply (rule FFVars_pick)
       apply (rule assms)
      apply assumption
     apply assumption
    apply (unfold Un_iff de_Morgan_disj tmp.FFVars_ctors)[1]
    apply (erule conjE)+
  apply (subst (asm) test3_pre.set_map, (rule supp_id_bound bij_id assms)+)+
    apply (rule conjI)
     apply assumption
    apply assumption

   apply (subst test3_pre.map_comp)
     apply (rule supp_id_bound bij_id)+
   apply (unfold id_o o_id)
   apply (rule arg_cong[of _ _ test3_ctor])
   apply (rule test3_pre.map_cong)
              apply (rule supp_id_bound bij_id refl)+
    apply (drule set_mp[rotated])
     apply assumption
    apply (unfold mem_Collect_eq case_prod_beta)
    apply (erule exE)
    apply (unfold comp_def pick_def)[1]
    apply (rule someI2)
     apply (unfold case_prod_beta)
     apply assumption
    apply (erule conjE)+
    apply assumption

(* repeated *)
apply (drule set_mp[rotated])
     apply assumption
    apply (unfold mem_Collect_eq case_prod_beta)
    apply (erule exE)
    apply (unfold comp_def pick_def)[1]
    apply (rule someI2)
     apply (unfold case_prod_beta)
     apply assumption
    apply (erule conjE)+
   apply assumption

  apply (rule trans)
   apply (rule tmp.vvsubst_ctor)
     apply (rule assms)
    apply (subst test3_pre.set_map, (rule supp_id_bound bij_id)+)
    apply (unfold image_id)
    apply (rule iffD2[OF disjoint_iff])
  apply (rule allI)
    apply (rule impI)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule sym)
     apply assumption
    apply (drule IHs)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption

(* noclash_tac repeated here *)
  apply (unfold noclash_test3_def)[1]
    apply (subst test3_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id noclash_test3_rel_def)[1]

apply (rule iffD2[OF disjoint_iff])
          apply (rule allI)
    apply (rule impI)

    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule sym)
     apply assumption
    apply (drule IHs)
    apply (unfold Un_iff de_Morgan_disj tmp.FFVars_ctors)[1]
    apply (erule conjE)+

    apply (rule conjI)
     apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<notin>)"]])
      apply (rule sym)
      apply assumption
     apply assumption
    apply hypsubst
    apply (subst (asm) test3_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id)[1]
    apply (rule FFVars_pick)
       apply (rule assms)
     apply assumption
  apply (unfold case_prod_beta)[1]
     apply assumption
    apply (unfold Un_iff de_Morgan_disj tmp.FFVars_ctors)[1]
    apply (erule conjE)+
  apply (subst (asm) test3_pre.set_map, (rule supp_id_bound bij_id assms)+)+
    apply (rule conjI)
     apply assumption
    apply assumption

   apply (subst test3_pre.map_comp)
     apply (rule supp_id_bound bij_id assms)+
   apply (unfold id_o o_id)
   apply (rule arg_cong[of _ _ test3_ctor])
   apply (rule test3_pre.map_cong)
              apply (rule supp_id_bound bij_id refl assms)+
    apply (drule set_mp[rotated])
     apply assumption
    apply (unfold mem_Collect_eq case_prod_beta)
    apply (erule exE)
    apply (unfold comp_def pick_def)[1]
    apply (rule someI2)
     apply (unfold case_prod_beta)
     apply assumption
    apply (erule conjE)+
    apply assumption

(* repeated *)
apply (drule set_mp[rotated])
     apply assumption
    apply (unfold mem_Collect_eq case_prod_beta)
    apply (erule exE)
    apply (unfold comp_def pick_def)[1]
    apply (rule someI2)
     apply (unfold case_prod_beta)
     apply assumption
    apply (erule conjE)+
  apply assumption
  done
  done

(* second implication *)

     apply (erule exE conjE)+
    subgoal for z
      apply (rule fresh_cases[of _ z])
       apply (rule iffD2[OF imsupp_supp_bound[OF cinfinite_imp_infinite[OF test3_pre.UNIV_cinfinite]] assms])
      apply hypsubst_thin
      apply (drule trans[rotated])
       apply (rule sym)
       apply (rule tmp.vvsubst_ctor)
         apply (rule supp_id_bound)
        apply (unfold imsupp_id)
        apply (rule Int_empty_right)
       apply (unfold noclash_test3_rel_def noclash_test3_def[symmetric])
       apply assumption
      apply (subst tmp.vvsubst_ctor)
         apply (rule assms)
        apply assumption+

      apply (subst (asm) tmp.inject)
      apply (erule exE conjE)+
      apply (unfold test3_pre.set_map[OF id_prems] image_id test3_pre.map_comp[OF id_prems supp_id_bound]
        id_o o_id tmp.vvsubst_rrename[symmetric]
        test3_pre.set_map[OF assms bij_id supp_id_bound]
        test3_pre.map_comp[OF assms bij_id supp_id_bound supp_id_bound]
        ext[of "test3_vvsubst _ _", OF tmp.vvsubst_comp[OF supp_id_bound], symmetric]
        ext[of "test3_vvsubst _ _", OF tmp.vvsubst_comp[OF assms], symmetric] image_comp comp_def[of FFVars_test3]
        tmp.FFVars_vvsubsts[OF supp_id_bound]
      )

      subgoal for x g
      apply (rule exI[of _ "map_test3_pre id snd id _ _ (map_test3_pre f id g id id x)"])
        apply (rule conjI)

         apply (subst test3_pre.map_comp)
               apply (rule assms supp_id_bound bij_id | assumption)+
         apply (unfold id_o o_id)
        defer

      apply (rule iffD2[OF test3_pre.mr_rel_map(1)])
            apply (rule assms bij_id supp_id_bound | assumption)+
         apply (unfold Grp_UNIV_id eq_OO id_o o_id)


        apply (rule test3_pre.mr_rel_mono_strong0[rotated -5])
               apply (rule ballI)
               apply (rule refl)
              apply (rule ballI)+
              apply (rule imp_refl)
             apply (rule ballI)
             apply (rule refl)
            apply (rule ballI)+
            apply (unfold Grp_UNIV_def OO_def comp_def)[1]
            apply (rule impI)
            apply (rule exI)
            apply (rule conjI)
             apply (rule refl)
            apply (unfold snd_conv)
            apply (drule IHs)
             apply (rule UNIV_I)
            apply (rotate_tac -1)
            apply (erule allE)
            apply (rotate_tac -1)
            apply (erule impE)
             apply (rule refl)
            apply (rule iffD1)
             apply (rule sym)
             apply (rotate_tac -1)
             apply assumption
            apply assumption

           apply (rule ballI impI)+
           apply (unfold Grp_UNIV_def OO_def comp_def)[1]
           apply (rule exI)
           apply (rule conjI)
            apply (rule refl)
           apply (unfold snd_conv)
           apply (tactic \<open>dmatch_tac @{context} @{thms IHs} 1\<close>)
            apply (rule UNIV_I)
           apply (tactic \<open>ematch_tac @{context} @{thms allE} 1\<close>)
           apply (tactic \<open>ematch_tac @{context} @{thms impE} 1\<close>)
            apply (rule refl)
           apply (rule iffD1)
            apply (rule sym)
            apply (rotate_tac -1)
            apply assumption
           apply assumption
               apply (rule assms supp_id_bound bij_id)+

         apply hypsubst_thin
        apply (rule iffD2[OF test3_pre.mr_rel_map(1)])
            apply (rule assms bij_id supp_id_bound | assumption)+
         apply (unfold Grp_UNIV_id eq_OO id_o o_id)
         apply (unfold mr_rel_test3_pre_def test3_pre.rel_map)

        

         apply (rule test3_pre.rel_refl_strong)

           apply (rule relcomppI)
            apply (unfold Grp_UNIV_def)[1]
            apply (rule refl)
           apply (subst (asm) test3_pre.set_map)
              apply (rule assms | assumption)+
           apply (unfold image_id set1_test3 Un_subset_iff)
           apply (erule conjE)+
        apply (rotate_tac -4)
           apply (drule set_mp[rotated])
            apply assumption
           apply (unfold mem_Collect_eq case_prod_beta)
           apply assumption
        

          apply (rule relcomppI)
           apply (unfold Grp_UNIV_def comp_def)[1]
           apply (rule refl)

          apply (subst (asm) test3_pre.set_map)
             apply (rule assms | assumption)+
          apply (unfold image_id)
          apply (rule exI)
          apply (rule conjI[rotated])+
            apply (rule refl)
        apply (rule tmp.vvsubst_comp[symmetric, unfolded comp_def, of _ id _ id, unfolded id_def, unfolded id_def[symmetric]])
        apply assumption
            apply (rule supp_id_bound)
          apply (unfold tmp.set_maps image_id)
          apply (rule subsetI)
          apply (erule conjE)+
          apply (rotate_tac -1)
          apply (erule set_mp)
          apply (rule UN_I)
           apply assumption+

         apply (rule relcomppI)
            apply (unfold Grp_UNIV_def)[1]
            apply (rule refl)
apply (subst (asm) test3_pre.set_map)
              apply (rule assms | assumption)+
           apply (unfold image_id set1_test3 Un_subset_iff)
         apply (erule conjE)+
         apply (rule exI)
         apply (rule conjI[rotated])+
           apply (rule refl)+
         apply (rule subsetI)
         apply (erule set_mp)
         apply (rule UN_I)
          apply assumption+
        apply (subst tmp.set_maps trans[OF comp_apply[symmetric] tmp.vvsubst_comp[symmetric]], (rule assms supp_inv_bound supp_comp_bound cinfinite_imp_infinite[OF test3_pre.UNIV_cinfinite] | assumption)+)+
        apply (unfold o_id)

        thm ex_avoiding_bij[of g "\<Union> (FFVars_test3 ` set4_test3_pre x) - set3_test3_pre x" "set3_test3_pre x" "imsupp f"]


        apply (rule exE[OF ex_avoiding_bij[of g "\<Union> (FFVars_test3 ` set4_test3_pre x) - set3_test3_pre x" "set3_test3_pre x" "imsupp f"]])
                apply assumption+
              apply (rule cinfinite_imp_infinite[OF test3_pre.UNIV_cinfinite])
             apply (rule card_of_minus_bound)
             apply (rule test3_pre.UNION_bound)
              apply (rule ordLess_ordLeq_trans)
               apply (rule test3_pre.set_bd)
              apply (rule var_test3_pre_class.large)
             apply (rule tmp.FFVars_bound_UNIV)
            apply assumption
           apply (rule test3_pre.set_bd_UNIV)
          apply assumption
         apply (rule iffD2[OF imsupp_supp_bound])
          apply (rule cinfinite_imp_infinite[OF test3_pre.UNIV_cinfinite])
         apply (rule assms)

        apply (erule conjE)+
        apply (rule trans)
         apply (rule arg_cong[of _ _ test3_ctor])
         apply (rule test3_pre.map_cong[rotated 6])
                    apply (rule refl)
                   apply (rule refl)
                  apply (rule refl)

                 apply (erule allE)
                 apply (erule impE)
                  prefer 2
                  apply (rule sym)
                  apply assumption
                 apply (rule conjI)
                  apply (rule UnI2)
                  apply assumption

                 defer (* NOT POSSIBLE *)

                 apply (rule tmp.vvsubst_cong[rotated 2])
                    apply (rule trans)
                     apply (rule comp_apply)
                    apply (rule arg_cong[of _ _ f])
                    apply (rule case_split[of "_ \<in> _", rotated])
        apply (rule trans)
                     apply (erule id_onD)
                     apply (rule DiffI)
                      apply (rule UN_I)
                        apply assumption+
                     apply (rule sym)
                     apply (rotate_tac -4)
                     apply (erule id_onD)
        apply (rule DiffI)
                      apply (rule UN_I)
        apply assumption+
                    apply (erule allE)
                    apply (erule impE)
                     prefer 2
                     apply (rule sym)
                     apply assumption
                    apply (rule conjI)
                     apply (rule UnI2)
                     apply assumption

                    defer (* IMPOSSIBLE *)

                    apply (rule refl)
                   apply (rule supp_comp_bound)
                     apply assumption
                    apply (rule assms)
                   apply (rule cinfinite_imp_infinite[OF test3_pre.UNIV_cinfinite])
                  apply (unfold comp_def[symmetric])[1]
                  apply (rule supp_comp_bound)
                    apply assumption
                   apply (rule assms)
                  apply (rule cinfinite_imp_infinite[OF test3_pre.UNIV_cinfinite])
                 apply (rule refl)
                apply (rule assms)
               apply assumption
              apply assumption
             apply (rule assms)
            apply assumption
           apply assumption


        subgoal for g'
          apply (rule iffD2[OF tmp.inject])
          apply (rule exI[of _ "inv g'"])
          apply (rule conjI)
           apply (rule bij_imp_bij_inv supp_inv_bound conjI | assumption)+
           apply (subst test3_pre.set_map, (rule assms | assumption)+)+
           apply (unfold image_comp[unfolded comp_def])
           apply (subst tmp.FFVars_vvsubsts)
            apply (unfold comp_def[symmetric])[1]
            apply (rule supp_comp_bound)
              apply assumption
             apply (rule assms)
            apply (rule cinfinite_imp_infinite[OF test3_pre.UNIV_cinfinite])
           (*apply (rule id_on_inv)
            apply assumption*)
           apply (unfold image_UN[symmetric])
           apply (unfold comp_def[symmetric])
           apply (unfold image_comp[symmetric])

           apply (rule iffD2[OF meta_eq_to_obj_eq[OF id_on_def]])
           apply (rule allI)
           apply (rule impI)
           apply (erule DiffE)
           apply (erule imageE)+
           apply (erule UN_E)
           apply hypsubst

          oops

coinductive test3_rel2 where
  "mr_rel_test3_pre id R id (test3_rel2 R) (test3_rel2 R) x y \<Longrightarrow> test3_rel2 R (test3_ctor x) (test3_ctor y)"
monos test3_pre.mr_rel_mono[OF supp_id_bound bij_id supp_id_bound]

lemma not_in_imsupp_image: "B \<inter> imsupp f = {} \<Longrightarrow> a \<in> B \<Longrightarrow> a \<notin> A \<Longrightarrow> a \<notin> f ` A"
  unfolding imsupp_def supp_def by fastforce

lemma in_rel:
  fixes f::"'a::var_test3_pre \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|"
  shows "test3_rel2 R (test3_vvsubst f id x) y =
    (\<exists>z. set1_test3 z \<subseteq> {(x, y). R x y} \<and> test3_vvsubst id fst z = x \<and> test3_vvsubst f snd z = y)"
  apply (rule iffI)
  subgoal sorry (* we know this works *)

  apply (erule exE conjE)+
  apply hypsubst_thin
  apply (subst trans[OF comp_apply[symmetric] tmp.vvsubst_comp[symmetric]])
    apply (rule supp_id_bound assms)+
  apply (unfold id_o o_id)
  subgoal for z
    apply (erule mp[OF mp[OF spec[OF tmp.fresh_induct_param[of UNIV, unfolded ball_UNIV],
      of "\<lambda>z. imsupp f \<union> FFVars_test3 z"
        "\<lambda>z \<rho>. set1_test3 z \<subseteq> {(x, y). R x y} \<longrightarrow> \<rho> = z \<longrightarrow> test3_rel2 R (test3_vvsubst f fst z) (test3_vvsubst f snd z)"
  ]], rotated -2])
      apply (rule refl)
    subgoal sorry (* trivial *)
    apply (rule impI)+
    apply (hypsubst)
    subgoal premises IHs for v
      apply (subgoal_tac "noclash_test3 v")
       prefer 2
  apply (unfold noclash_test3_def)[1]
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
        apply (drule IHs)
         apply (unfold Un_iff de_Morgan_disj tmp.FFVars_ctors)+
        apply (erule conjE)+
       apply ((rule conjI)?, assumption)+
      apply (subgoal_tac "set3_test3_pre v \<inter> imsupp f = {}")
       prefer 2
apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply (drule IHs)
         apply (unfold Un_iff de_Morgan_disj)+
         apply (erule conjE)+
         apply assumption+

      apply (rule iffD2[OF arg_cong3[OF refl, of _ _ _ _ test3_rel2]])
        apply (rule tmp.vvsubst_ctor, (rule assms | assumption)+)+

      apply (rule test3_rel2.intros)

      apply (rule iffD2[OF test3_pre.mr_rel_map(1)])
            apply (rule assms supp_id_bound bij_id)+
      apply (unfold id_o o_id)

      apply (unfold mr_rel_test3_pre_def)
      apply (subgoal_tac "map_test3_pre f snd id (test3_vvsubst f snd) (test3_vvsubst f snd) v = map_test3_pre id snd id (test3_vvsubst f snd) (test3_vvsubst f snd) (map_test3_pre f id id id id v)")
       prefer 2
       apply (subst test3_pre.map_comp)
          apply (rule assms bij_id supp_id_bound)+
       apply (unfold id_o o_id)
       apply (rule refl)
      apply (simp only:)

      apply (rule iffD2[OF test3_pre.rel_map(2)])
      apply (rule test3_pre.rel_refl_strong)

        apply (rule relcomppI)
         apply (rule GrpI)
          apply (rule refl)
         apply (rule UNIV_I)
        apply (subst (asm) test3_pre.set_map)
           apply (rule assms supp_id_bound bij_id)+
        apply (insert IHs(5))
        apply (unfold image_id set1_test3 Un_subset_iff)[1]
        apply (erule conjE)+
        apply (drule set_mp[rotated])
         apply assumption
        apply (unfold mem_Collect_eq case_prod_beta)[1]
        apply assumption

       apply (rule relcomppI)
        apply (rule GrpI)
         apply (rule refl)
        apply (rule UNIV_I)
       apply (subst (asm) test3_pre.set_map)
          apply (rule assms bij_id supp_id_bound)+
       apply (unfold image_id)
       apply (rule IHs[unfolded test3_rel_def atomize_imp[symmetric]], assumption)
         apply (rule UNIV_I)
        apply (unfold set1_test3 Un_subset_iff UN_subset_iff)[1]
        apply (erule conjE)+
        apply (drule bspec, assumption)
        apply assumption
       apply (rule refl)

apply (rule relcomppI)
        apply (rule GrpI)
         apply (rule refl)
        apply (rule UNIV_I)
       apply (subst (asm) test3_pre.set_map)
          apply (rule assms bij_id supp_id_bound)+
       apply (unfold image_id)
       apply (rule IHs[unfolded test3_rel_def atomize_imp[symmetric]], assumption)
         apply (rule UNIV_I)
        apply (unfold set1_test3 Un_subset_iff UN_subset_iff)[1]
        apply (erule conjE)+
        apply (drule bspec, assumption)
        apply assumption
      apply (rule refl)
      done
    done
  done

lemma in_rel_alt:
  fixes f::"'a::var_test3_pre \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|"
  shows "test3_rel R (test3_vvsubst f id x) y =
    (\<exists>z. set1_test3 z \<subseteq> {(x, y). R x y} \<and> test3_vvsubst id fst z = x \<and> test3_vvsubst f snd z = y)"
  apply (rule iffI)
  subgoal sorry (* we know this works *)

  apply (erule exE conjE)+
  apply hypsubst_thin
  apply (subst trans[OF comp_apply[symmetric] tmp.vvsubst_comp[symmetric]])
    apply (rule supp_id_bound assms)+
  apply (unfold id_o o_id)
  subgoal for z
    apply (erule mp[OF mp[OF spec[OF tmp.fresh_induct_param[of UNIV, unfolded ball_UNIV],
      of "\<lambda>z. imsupp f \<union> FFVars_test3 z"
        "\<lambda>z \<rho>. set1_test3 z \<subseteq> {(x, y). R x y} \<longrightarrow> \<rho> = z \<longrightarrow> test3_rel R (test3_vvsubst f fst z) (test3_vvsubst f snd z)"
  ]], rotated -2])
      apply (rule refl)
    subgoal sorry (* trivial *)
    apply (rule impI)+
    apply (hypsubst)
    subgoal premises IHs for v
      apply (subgoal_tac "noclash_test3 v")
       prefer 2
  apply (unfold noclash_test3_def)[1]
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
        apply (drule IHs)
         apply (unfold Un_iff de_Morgan_disj tmp.FFVars_ctors)+
        apply (erule conjE)+
       apply ((rule conjI)?, assumption)+
      apply (subgoal_tac "set3_test3_pre v \<inter> imsupp f = {}")
       prefer 2
apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply (drule IHs)
         apply (unfold Un_iff de_Morgan_disj)+
         apply (erule conjE)+
         apply assumption+

      apply (rule iffD2[OF arg_cong3[OF refl, of _ _ _ _ test3_rel]])
        apply (rule tmp.vvsubst_ctor, (rule assms | assumption)+)+

      apply (unfold test3_rel_def)
      apply (rule iffD2[OF fun_cong[OF tmp.rel_ctor]])
        apply (unfold Un_empty_right image_id)
        apply (subst test3_pre.set_map, (rule assms bij_id supp_id_bound)+)+
        apply (unfold image_id)
      apply (rule iffD2[OF disjoint_iff])
        apply (rule allI impI)+

        apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<notin>)"]])
      apply (rule trans)
         apply (rule arg_cong[of _ _ FFVars_test3])
         apply (rule tmp.vvsubst_ctor[symmetric])
            apply (rule assms | assumption)+
         apply (rule tmp.FFVars_vvsubsts)
      apply (rule assms)
        apply (erule not_in_imsupp_image)
         apply assumption
        apply (drule IHs)
        apply (unfold Un_iff de_Morgan_disj)
        apply (erule conjE)+
        apply assumption

       apply (unfold noclash_test3_rel_def)
       apply (subst test3_pre.set_map, (rule assms bij_id supp_id_bound)+)+
       apply (unfold image_id image_comp[unfolded comp_def])
       apply (subst tmp.FFVars_vvsubsts)
        apply (rule assms)
       apply (unfold image_UN[symmetric] image_Un[symmetric])
      apply (rule iffD2[OF disjoint_iff])
       apply (rule allI impI)+
       apply (erule not_in_imsupp_image)
        apply assumption
       apply (drule IHs)
       apply (unfold Un_iff de_Morgan_disj tmp.FFVars_ctors)[1]
       apply (erule conjE)+
       apply (rule conjI)
        apply assumption+

      apply (unfold CCTOR_eq)
      apply (unfold CCTOR5_def)
      apply (rule exI)
      apply (rule conjI)
       apply (rule refl)

      apply (subst test3_pre.map_comp)
         apply (rule assms supp_id_bound bij_id)+
      apply (unfold id_o o_id)

      apply (rule iffD2[OF test3_pre.mr_rel_map(1)])
            apply (rule assms supp_id_bound bij_id)+
      apply (unfold id_o o_id)

      apply (unfold mr_rel_test3_pre_def)
      apply (subgoal_tac "map_test3_pre f snd id (test3_vvsubst f snd) (test3_vvsubst f snd) v = map_test3_pre id snd id (test3_vvsubst f snd) (test3_vvsubst f snd) (map_test3_pre f id id id id v)")
       prefer 2
       apply (subst test3_pre.map_comp)
          apply (rule assms bij_id supp_id_bound)+
       apply (unfold id_o o_id)
       apply (rule refl)
      apply (simp only:)

      apply (rule iffD2[OF test3_pre.rel_map(2)])
      apply (rule test3_pre.rel_refl_strong)

        apply (rule relcomppI)
         apply (rule GrpI)
          apply (rule refl)
         apply (rule UNIV_I)
        apply (subst (asm) test3_pre.set_map)
           apply (rule assms supp_id_bound bij_id)+
        apply (insert IHs(5))
        apply (unfold image_id set1_test3 Un_subset_iff)[1]
        apply (erule conjE)+
        apply (drule set_mp[rotated])
         apply assumption
        apply (unfold mem_Collect_eq case_prod_beta)[1]
        apply assumption

       apply (rule relcomppI)
        apply (rule GrpI)
         apply (rule refl)
        apply (rule UNIV_I)
       apply (unfold comp_def snd_conv)[1]
       apply (subst (asm) test3_pre.set_map)
          apply (rule assms bij_id supp_id_bound)+
       apply (unfold image_id)
       apply (rule IHs[unfolded test3_rel_def atomize_imp[symmetric]], assumption)
         apply (rule UNIV_I)
        apply (unfold set1_test3 Un_subset_iff UN_subset_iff)[1]
        apply (erule conjE)+
        apply (drule bspec, assumption)
        apply assumption
       apply (rule refl)

apply (rule relcomppI)
        apply (rule GrpI)
         apply (rule refl)
        apply (rule UNIV_I)
       apply (unfold comp_def snd_conv)[1]
       apply (subst (asm) test3_pre.set_map)
          apply (rule assms bij_id supp_id_bound)+
       apply (unfold image_id)
       apply (rule IHs[unfolded test3_rel_def atomize_imp[symmetric]], assumption)
         apply (rule UNIV_I)
        apply (unfold set1_test3 Un_subset_iff UN_subset_iff)[1]
        apply (erule conjE)+
        apply (drule bspec, assumption)
        apply assumption
      apply (rule refl)
      done
    done
  done

end