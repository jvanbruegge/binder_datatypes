theory Least_Fixpoint2
  imports "Binders.MRBNF_Composition" "Binders.MRBNF_FP"
begin

declare [[mrbnf_internals]]

(*
binder_datatype 'a term =
  Var 'a
| App "'a term" "'a term"
| Lam2 x::'a t::"'a term" x2::'a t2::"'a term" binds x in t, binds x2 in t t2
*)

ML \<open>
val ctor_T1_Ts = [
  [@{typ 'var}],
  [@{typ 'rec}, @{typ 'rec}],
  [@{typ 'b1}, @{typ "'brec1"}, @{typ 'b2}, @{typ "'brec2"}]
]
\<close>

ML \<open>
val T1 = BNF_FP_Util.mk_sumprodT_balanced ctor_T1_Ts
val name1 = "term";
val rel = [[([], [0]), ([], [0, 1])]];
Multithreading.parallel_proofs := 4
\<close>

declare [[quick_and_dirty]]
declare [[ML_print_depth=1000]]
declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val Xs = map dest_TFree []
  val resBs = map dest_TFree [@{typ 'var}, @{typ 'b1}, @{typ 'b2}, @{typ 'brec1}, @{typ 'brec2}, @{typ 'rec}]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify1 = Binding.prefix_name (name1 ^ "_pre_")
  val accum = (MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds)

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf1, tys1), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify1 flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'b1}, MRBNF_Def.Bound_Var),
      (dest_TFree @{typ 'b2}, MRBNF_Def.Bound_Var)] T1
    (accum, lthy)
  val _ = @{print} "comp"

  (* Step 2: Seal the pre-MRBNF with a typedef *)
  val ((mrbnf1, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name1 ^ "_pre")) true (fst tys1) [] mrbnf1 lthy
  val _ = @{print} "seal"

  (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
  val (bnf1, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf1 lthy
  val _ = @{print} "register"
in lthy end
\<close>
print_theorems
print_mrbnfs

declare [[quick_and_dirty=false]]

lemmas infinite_UNIV = cinfinite_imp_infinite[OF term_pre.UNIV_cinfinite]

(********************** BINDER FIXPOINT CONSTRUCTION **************************************)

typ "('a, 'b1, 'b2, 'brec1, 'brec2, 'rec) term_pre"

datatype ('a::var_term_pre) raw_term = raw_term_ctor "('a, 'a, 'a, 'a raw_term, 'a raw_term, 'a raw_term) term_pre"

primrec permute_raw_term :: "('a::var_term_pre \<Rightarrow> 'a) \<Rightarrow> 'a raw_term \<Rightarrow> 'a raw_term" where
  "permute_raw_term f (raw_term_ctor x) = raw_term_ctor (map_term_pre f f f id id id (
    map_term_pre id id id (permute_raw_term f) (permute_raw_term f) (permute_raw_term f) x
  ))"

lemma permute_raw_simps:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "permute_raw_term f (raw_term_ctor x) = raw_term_ctor (map_term_pre f f f (permute_raw_term f) (permute_raw_term f) (permute_raw_term f) x)"
  apply (rule trans)
   apply (rule permute_raw_term.simps)
  apply (subst term_pre.map_comp)
      apply (rule supp_id_bound bij_id assms)+
  apply (unfold id_o o_id)
  apply (rule refl)
  done

inductive free_raw_term :: "'a::var_term_pre \<Rightarrow> 'a raw_term \<Rightarrow> bool" where
  "a \<in> set1_term_pre x \<Longrightarrow> free_raw_term a (raw_term_ctor x)"
| "z \<in> set4_term_pre x \<Longrightarrow> free_raw_term a z \<Longrightarrow> a \<notin> set2_term_pre x \<union> set3_term_pre x \<Longrightarrow> free_raw_term a (raw_term_ctor x)"
| "z \<in> set5_term_pre x \<Longrightarrow> free_raw_term a z \<Longrightarrow> a \<notin> set3_term_pre x \<Longrightarrow> free_raw_term a (raw_term_ctor x)"
| "z \<in> set6_term_pre x \<Longrightarrow> free_raw_term a z \<Longrightarrow> free_raw_term a (raw_term_ctor x)"

definition FVars_raw_term :: "'a::var_term_pre raw_term \<Rightarrow> 'a set" where
  "FVars_raw_term x \<equiv> { a. free_raw_term a x }"

definition "suppGr f \<equiv> {(x, f x) | x. f x \<noteq> x}"

coinductive alpha_term :: "'a::var_term_pre raw_term \<Rightarrow> 'a raw_term \<Rightarrow> bool" where
  "\<lbrakk> bij g ; |supp g| <o |UNIV::'a set| ;
    id_on (\<Union>(FVars_raw_term ` set4_term_pre x) - (set2_term_pre x \<union> set3_term_pre x)) g ;
    bij f2 ; |supp f2| <o |UNIV::'a set| ; id_on (\<Union>(FVars_raw_term ` set5_term_pre x) - set3_term_pre x) f2 ;
    eq_on (set3_term_pre x) f2 g ;
    mr_rel_term_pre id g g (\<lambda>x. alpha_term (permute_raw_term g x)) (\<lambda>x. alpha_term (permute_raw_term f2 x)) alpha_term x y
  \<rbrakk> \<Longrightarrow> alpha_term (raw_term_ctor x) (raw_term_ctor y)"
monos conj_context_mono term_pre.mr_rel_mono[OF supp_id_bound]

type_synonym 'a raw_term_pre = "('a, 'a, 'a, 'a raw_term, 'a raw_term, 'a raw_term) term_pre"

definition avoid_raw_term :: "'a::var_term_pre raw_term_pre \<Rightarrow> 'a set \<Rightarrow> 'a raw_term_pre" where
  "avoid_raw_term x A \<equiv> SOME y. (set2_term_pre y \<union> set3_term_pre y) \<inter> A = {} \<and> alpha_term (raw_term_ctor x) (raw_term_ctor y)"

typedef ('a::var_term_pre) "term" = "(UNIV::'a raw_term set) // { (x, y). alpha_term x y }"
  apply (rule exI)
  apply (rule quotientI)
  apply (rule UNIV_I)
  done

abbreviation "TT_abs \<equiv> quot_type.abs alpha_term Abs_term"
abbreviation "TT_rep \<equiv> quot_type.rep Rep_term"

type_synonym 'a term_pre' = "('a, 'a, 'a, 'a term, 'a term, 'a term) term_pre"

definition term_ctor :: "'a::var_term_pre term_pre' \<Rightarrow> 'a term" where
  "term_ctor x \<equiv> TT_abs (raw_term_ctor (map_term_pre id id id TT_rep TT_rep TT_rep x))"

definition permute_term :: "('a::var_term_pre \<Rightarrow> 'a) \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "permute_term f x \<equiv> TT_abs (permute_raw_term f (TT_rep x))"

definition FVars_term :: "'a::var_term_pre term \<Rightarrow> 'a set" where
  "FVars_term x \<equiv> FVars_raw_term (TT_rep x)"

definition avoid_term :: "'a::var_term_pre term_pre' \<Rightarrow> 'a set \<Rightarrow> 'a term_pre'" where
  "avoid_term x A \<equiv> map_term_pre id id id TT_abs TT_abs TT_abs (
    avoid_raw_term (map_term_pre id id id TT_rep TT_rep TT_rep x) A)"

inductive subshape_term_term :: "'a::var_term_pre raw_term \<Rightarrow> 'a raw_term \<Rightarrow> bool" where
  "\<lbrakk> bij f ; |supp f| <o |UNIV::'a set| ; alpha_term (permute_raw_term f y) z ;
    z \<in> set4_term_pre x \<union> set5_term_pre x \<union> set6_term_pre x \<rbrakk> \<Longrightarrow> subshape_term_term y (raw_term_ctor x)"

definition noclash_raw_term :: "'a::var_term_pre raw_term_pre \<Rightarrow> bool" where
  "noclash_raw_term x \<equiv> (set2_term_pre x \<union> set3_term_pre x) \<inter> (set1_term_pre x \<union> \<Union>(FVars_raw_term ` set6_term_pre x)) = {}"

definition noclash_term :: "'a::var_term_pre term_pre' \<Rightarrow> bool" where
  "noclash_term x \<equiv> (set2_term_pre x \<union> set3_term_pre x) \<inter> (set1_term_pre x \<union> \<Union>(FVars_term ` set6_term_pre x)) = {}"

(****************** PROOFS ******************)

lemma permute_raw_ids: "permute_raw_term id x = x"
  apply (rule raw_term.induct[of _ x])
  apply (rule trans)
   apply (rule permute_raw_simps)
    apply (rule bij_id supp_id_bound)+
  apply (rule trans)
   apply (rule arg_cong[of _ _ raw_term_ctor])
   apply (rule trans[rotated])
    apply (rule term_pre.map_id)
   apply (rule term_pre.map_cong)
                   apply (rule bij_id supp_id_bound)+
         apply (rule refl trans[OF _ id_apply[symmetric]] | assumption)+
  done

lemmas permute_raw_id0s = permute_raw_ids[abs_def, unfolded id_def[symmetric], THEN meta_eq_to_obj_eq]

lemma permute_raw_comps:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
    and g_prems: "bij g" "|supp g| <o |UNIV::'a set|"
  shows "permute_raw_term f (permute_raw_term g x) = permute_raw_term (f \<circ> g) x"
  apply (rule raw_term.induct[of _ x])
  apply (subst permute_raw_simps, (rule assms bij_comp supp_comp_bound infinite_UNIV)+)+
  apply (subst term_pre.map_comp)
      apply (rule assms)+
  apply (rule arg_cong[OF term_pre.map_cong])
                  apply (rule assms bij_comp supp_comp_bound infinite_UNIV refl)+
    apply (rule trans[OF comp_apply], assumption)+
  done

lemma permute_raw_comp0s:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
    and g_prems: "bij g" "|supp g| <o |UNIV::'a set|"
  shows "permute_raw_term f \<circ> permute_raw_term g = permute_raw_term (f \<circ> g)"
  apply (rule ext)
  apply (rule trans[OF comp_apply])
  apply (rule permute_raw_comps)
     apply (rule assms)+
  done

lemma FVars_raw_intros:
  "a \<in> set1_term_pre x \<Longrightarrow> a \<in> FVars_raw_term (raw_term_ctor x)"
  "z \<in> set4_term_pre x \<Longrightarrow> a \<in> FVars_raw_term z \<Longrightarrow> a \<notin> set2_term_pre x \<union> set3_term_pre x \<Longrightarrow> a \<in> FVars_raw_term (raw_term_ctor x)"
  "z \<in> set5_term_pre x \<Longrightarrow> a \<in> FVars_raw_term z \<Longrightarrow> a \<notin> set3_term_pre x \<Longrightarrow> a \<in> FVars_raw_term (raw_term_ctor x)"
  "z \<in> set6_term_pre x \<Longrightarrow> a \<in> FVars_raw_term z \<Longrightarrow> a \<in> FVars_raw_term (raw_term_ctor x)"
     apply (unfold FVars_raw_term_def mem_Collect_eq)
     apply (erule free_raw_term.intros | assumption)+
  done

lemma FVars_raw_ctors:
  "FVars_raw_term (raw_term_ctor x) = set1_term_pre x \<union> (\<Union>(FVars_raw_term ` set4_term_pre x) - (set2_term_pre x \<union> set3_term_pre x))
   \<union> (\<Union>(FVars_raw_term ` set5_term_pre x) - set3_term_pre x) \<union> \<Union>(FVars_raw_term ` set6_term_pre x)"
  apply (rule subset_antisym)
   apply (unfold FVars_raw_term_def)[1]
   apply (rule subsetI)
   apply (unfold mem_Collect_eq)
   apply (erule free_raw_term.cases)
      (* REPEAT_DETERM *)
      apply (drule iffD1[OF raw_term.inject])
      apply hypsubst_thin
      apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 1] 1\<close>)
      apply assumption
    (* repeated *)
     apply (drule iffD1[OF raw_term.inject])
     apply hypsubst_thin
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 2] 1\<close>)
     apply (rule DiffI)
      apply (rule UN_I)
       apply (unfold mem_Collect_eq)
       apply assumption+
    (* repeated *)
     apply (drule iffD1[OF raw_term.inject])
     apply hypsubst_thin
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 3] 1\<close>)
     apply (rule DiffI)
      apply (rule UN_I)
       apply (unfold mem_Collect_eq)
       apply assumption+
    (* repeated *)
     apply (drule iffD1[OF raw_term.inject])
     apply hypsubst_thin
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 4] 1\<close>)
      apply (rule UN_I)
       apply (unfold mem_Collect_eq)
       apply assumption+
    (* END REPEAT_DETERM *)
  apply (rule subsetI)
  apply (erule UnE)+
     apply (((erule DiffE UN_E)+)?, erule FVars_raw_intros, (assumption+)?)+
  done

lemma FVars_raw_permute_leq:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
  shows "free_raw_term a x \<Longrightarrow> f a \<in> FVars_raw_term (permute_raw_term f x)"
  apply (erule free_raw_term.induct[of _ x])
  (* REPEAT_DETERM *)
     apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
     apply (subst term_pre.set_map, (rule assms supp_id_bound bij_id)+)+
     apply (unfold image_comp[unfolded comp_def])
             apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 1] 1\<close>)
     apply (rule DiffI)?
     apply (rule imageI | (rule UN_I, assumption))
     apply assumption
    apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
  (* repeated *)
     apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
     apply (subst term_pre.set_map, (rule assms supp_id_bound bij_id)+)+
     apply (unfold image_comp[unfolded comp_def])
             apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 2] 1\<close>)
    apply (rule DiffI)?
     apply (rule imageI | (rule UN_I, assumption))
     apply assumption
    apply (unfold image_Un[symmetric])[1]
    apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
  (* repeated *)
     apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
     apply (subst term_pre.set_map, (rule assms supp_id_bound bij_id)+)+
     apply (unfold image_comp[unfolded comp_def])
             apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 3] 1\<close>)
    apply (rule DiffI)?
     apply (rule imageI | (rule UN_I, assumption))
     apply assumption
    apply ((unfold image_Un[symmetric])[1])?
    apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
  (* repeated *)
     apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
     apply (subst term_pre.set_map, (rule assms supp_id_bound bij_id)+)+
     apply (unfold image_comp[unfolded comp_def])
             apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 4] 1\<close>)
    apply (rule DiffI)?
     apply (rule imageI | (rule UN_I, assumption))
     apply assumption
    apply ((unfold image_Un[symmetric])[1])?
    apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
  (* END REPEAT_DETERM *)
  done

lemma FVars_raw_permutes:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
  shows "FVars_raw_term (permute_raw_term f x) = f ` FVars_raw_term x"
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (subst (asm) FVars_raw_term_def)
   apply (drule iffD1[OF mem_Collect_eq])
   apply (drule FVars_raw_permute_leq[rotated -1])
     prefer 3 (* 2 * nvars + 1 *)
     apply (subst (asm) permute_raw_comps)
         prefer 5 (* 4 * nvars + 1 *)
         apply (subst (asm) inv_o_simp1, rule assms)+
         apply (unfold permute_raw_ids)
         apply (erule iffD2[OF image_in_bij_eq, rotated])
         apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  apply (rule subsetI)
  apply (erule imageE)
  apply hypsubst
  apply (subst (asm) FVars_raw_term_def)
  apply (drule iffD1[OF mem_Collect_eq])
  apply (erule FVars_raw_permute_leq[rotated -1])
   apply (rule assms)+
  done

lemmas Un_bound = infinite_regular_card_order_Un[OF term_pre.bd_infinite_regular_card_order]
lemmas UN_bound = regularCard_UNION_bound[OF term_pre.bd_Cinfinite term_pre.bd_regularCard]

lemma FVars_raw_bds: "|FVars_raw_term x| <o natLeq"
  apply (rule raw_term.induct[of _ x])
  apply (unfold FVars_raw_ctors)
  apply (rule Un_bound term_pre.set_bd ordLeq_ordLess_trans[OF card_of_diff] UN_bound | assumption)+
  done

lemmas FVars_raw_bd_UNIVs = FVars_raw_bds[THEN ordLess_ordLeq_trans, OF var_term_pre_class.large]

lemma alpha_refls:
  fixes x::"'a::var_term_pre raw_term"
  shows "alpha_term x x"
proof -
  have x: "\<forall>(x::'a raw_term) y. x = y \<longrightarrow> alpha_term x y"
    apply (rule allI impI)+
    apply (erule alpha_term.coinduct)
    apply hypsubst_thin
    apply (unfold triv_forall_equality)
    subgoal for x
      apply (rule raw_term.exhaust[of x])
      apply hypsubst_thin
      apply (rule exI)+
      apply (rule conjI, rule refl supp_id_bound bij_id id_on_id eq_on_refl)+
      apply (unfold term_pre.mr_rel_id[symmetric] permute_raw_ids)
      apply (rule term_pre.rel_refl_strong)
        apply (rule disjI1 refl)+
      done
    done

  show ?thesis by (rule x[THEN spec, THEN spec, THEN mp[OF _ refl]])
qed

lemma alpha_bijs:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
    and g_prems: "bij g" "|supp g| <o |UNIV::'a set|"
  shows "eq_on (FVars_raw_term x) f g \<Longrightarrow> alpha_term x y \<Longrightarrow> alpha_term (permute_raw_term f x) (permute_raw_term g y)"
proof -
  have x: "\<forall>(x::'a raw_term) y. (\<exists>x' y' f g. bij f \<and> |supp f| <o |UNIV::'a set| \<and> bij g \<and> |supp g| <o |UNIV::'a set|
    \<and> x = permute_raw_term f x' \<and> y = permute_raw_term g y' \<and> eq_on (FVars_raw_term x') f g \<and> alpha_term x' y')
    \<longrightarrow> alpha_term x y"
    apply (rule allI impI)+
    apply (erule alpha_term.coinduct)
    apply (erule exE conjE)+
    apply (erule alpha_term.cases)
    apply hypsubst
    apply (unfold triv_forall_equality)
    subgoal for f g \<sigma> x f2 y
      apply (rule exI[of _ "g \<circ> \<sigma> \<circ> inv f"])
      apply (rule exI)
      apply (rule exI[of _ "g \<circ> f2 \<circ> inv f"])
      apply (rule exI)+
      apply (rule conjI, rule permute_raw_simps, (rule supp_id_bound bij_id | assumption)+)+
      apply (rule conjI, (rule bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound infinite_UNIV | assumption)+)+

      apply (subst term_pre.set_map, assumption+)+
      apply (unfold image_Un[symmetric] image_comp[unfolded comp_def])
      apply (subst FVars_raw_permutes, assumption+)+
      apply (unfold image_UN[symmetric])
      apply (subst image_set_diff[OF bij_is_inj, symmetric], assumption+)+

      apply (rule conjI)
       apply (rule id_onI)
       apply (erule imageE)
       apply hypsubst
       apply (rule trans[OF comp_apply])
       apply (rule trans[OF arg_cong[OF inv_simp1]])
        apply assumption
       apply (rule trans[OF comp_apply])
       apply (rule trans[OF arg_cong[of _ _ g]])
        apply (erule id_onD)
        apply assumption
       apply (rule sym)
       apply (erule eq_onD)
       apply (erule DiffE)
       apply (erule UN_E)
       apply (erule FVars_raw_intros)
        apply assumption+

      apply (rule conjI, (rule bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound infinite_UNIV | assumption)+)+

      apply (rule conjI)
       apply (rule id_onI)
       apply (erule imageE)
       apply hypsubst
       apply (rule trans[OF comp_apply])
       apply (rule trans[OF arg_cong[OF inv_simp1]])
        apply assumption
       apply (rule trans[OF comp_apply])
       apply (rule trans[OF arg_cong[of _ _ g]])
        apply (erule id_onD)
        apply assumption
       apply (rule sym)
       apply (erule eq_onD)
       apply (erule DiffE)
       apply (erule UN_E)
       apply (erule FVars_raw_intros)
        apply assumption+

      apply (rule conjI)
       apply (rule eq_on_comp)
        apply (unfold image_comp inv_o_simp1 image_id)[1]
        apply (rule eq_on_comp)
         apply (rule eq_on_refl)
        apply assumption
      apply (rule eq_on_refl)

      apply (rule iffD2[OF term_pre.mr_rel_map(1)])
                apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound)+
      apply (unfold id_o o_id)
      apply (rule iffD2[OF term_pre.mr_rel_map(3)])
                 apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound)+
      apply (unfold comp_assoc inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq relcompp_conversep_Grp Grp_OO)
      apply (subst inv_o_simp1, assumption)+
      apply (unfold id_o o_id comp_assoc[symmetric])
      apply (subst inv_o_simp1, assumption)+
      apply (unfold id_o o_id)
      apply (erule term_pre.mr_rel_mono_strong0[rotated -7])
        (* REPEAT_DETERM *)
                     apply (rule ballI)
                     apply (rule trans)
                      apply (rule id_apply)
                     apply (rule sym)
                     apply (rule trans[OF comp_apply])
                     apply (rule inv_f_eq[OF bij_is_inj])
                      apply assumption
                     apply (rule sym)
                     apply (erule eq_onD)
                     apply (erule FVars_raw_intros)
        (* END REPEAT_DETERM *)
                    apply (rule ballI, rule refl)+
        (* REPEAT_DETERM *)
                  apply (rule ballI)
                  apply (rule ballI)
                  apply (rule impI)
                  apply (rule disjI1)
                  apply (rule exI)+
                  apply (rule conjI[rotated])+
                         apply assumption
                        apply (rule eq_on_refl)
                       apply (rule refl)
                      apply (rule trans)
                       apply (rule permute_raw_comps)
                          apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound)+
                      apply (unfold comp_assoc)
                      apply (subst inv_o_simp1, assumption)
                      apply (unfold o_id)
                      apply (rule trans)
                       apply (rule permute_raw_comps[symmetric])
                          apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound)+
                      apply (rule refl)
                     apply assumption+
        (* repeated *)
                  apply (rule ballI)
                  apply (rule ballI)
                  apply (rule impI)
                  apply (rule disjI1)
                  apply (rule exI)+
                  apply (rule conjI[rotated])+
                         apply assumption
                        apply (rule eq_on_refl)
                       apply (rule refl)
                      apply (rule trans)
                       apply (rule permute_raw_comps)
                          apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound)+
                      apply (unfold comp_assoc)
                      apply (subst inv_o_simp1, assumption)
                      apply (unfold o_id)
                      apply (rule trans)
                       apply (rule permute_raw_comps[symmetric])
                          apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound)+
                      apply (rule refl)
                     apply assumption+
        (* repeated, rec free case *)
                  apply (rule ballI)
                  apply (rule ballI)
                  apply (rule impI)
                  apply (rule disjI1)
                apply (rule exI)+
                  apply (rule conjI[rotated])+
                       apply assumption
                      apply (erule eq_on_mono[rotated -1])
                      apply (rule subsetI)
                      apply (erule FVars_raw_intros)
                      apply assumption
                     apply (rule refl)+
                   apply assumption+
            (* END REPEAT_DETERM *)
               apply (rule supp_id_bound bij_id supp_comp_bound bij_comp infinite_UNIV supp_inv_bound bij_imp_bij_inv | assumption)+
      done
    done

  show "eq_on (FVars_raw_term x) f g \<Longrightarrow> alpha_term x y \<Longrightarrow> alpha_term (permute_raw_term f x) (permute_raw_term g y)"
    apply (rule x[THEN spec, THEN spec, THEN mp])
    apply (rule exI)+
    apply (rule conjI[rotated])+
           apply assumption+
         apply (rule refl)+
       apply (rule assms)+
    done
qed

lemma alpha_bij_eqs:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
  shows "alpha_term (permute_raw_term f x) (permute_raw_term f y) = alpha_term x y"
  apply (rule iffI)
   apply (drule alpha_bijs[rotated -1])
        prefer 6 (* 5 * nvars + 1 *)
    (* REPEAT_DETERM *)
        apply (subst (asm) permute_raw_comps)
            prefer 5 (* 4 * nvars + 1 *)
            apply (subst (asm) inv_o_simp1, rule assms)
    (* repeated *)
            apply (subst (asm) permute_raw_comps)
                prefer 5 (* 4 * nvars + 1 *)
                apply (subst (asm) inv_o_simp1, rule assms)
    (* END REPEAT_DETERM *)
                apply (unfold permute_raw_ids)
                apply assumption
               apply (rule bij_imp_bij_inv supp_inv_bound assms)+
   apply (rule eq_on_refl)
  apply (erule alpha_bijs[rotated -1])
      apply (rule assms eq_on_refl)+
  done

lemma alpha_bij_eq_invs:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
  shows "alpha_term (permute_raw_term f x) y = alpha_term x (permute_raw_term (inv f) y)"
  apply (rule trans)
   apply (rule alpha_bij_eqs[symmetric])
    prefer 3 (* 2 * nvars + 1 *)
    apply (subst permute_raw_comps)
        prefer 5 (* 4 * nvars + 1 *)
        apply (subst inv_o_simp1, rule assms)+
        apply (unfold permute_raw_ids)
        apply (rule refl)
       apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  done

lemma alpha_FVars: "alpha_term x y \<Longrightarrow> FVars_raw_term x = FVars_raw_term y"
proof -
  have x: "\<forall>y. alpha_term x y \<longrightarrow> FVars_raw_term x = FVars_raw_term y"
    apply (rule raw_term.induct[of _ x])
    subgoal premises IHs for x
      apply (rule allI)
      apply (rule impI)
      apply (erule alpha_term.cases)
      apply (drule iffD1[OF raw_term.inject])
      apply hypsubst
      apply (unfold FVars_raw_ctors)
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
         apply (rule sym)
         apply (erule term_pre.mr_rel_set[OF supp_id_bound, unfolded image_id, rotated -1])
            apply (rule supp_id_bound bij_id | assumption)+
        (* REPEAT_DETERM *)
        apply (rule sym)
        apply (rule trans)
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
           apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
            apply (erule term_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
         prefer 2
          apply (unfold image_Un[symmetric])[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj, symmetric])
          apply assumption
         apply (erule id_on_image)
        apply (unfold image_UN)[1]
        apply (rule sym)
        apply (rule rel_set_UN_D)
        apply (erule term_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF term_pre.mr_rel_mono_strong[rotated -4]])
        (* REPEAT_DETERM *)
                    apply (rule ballI)
                    apply (rule ballI)
                    apply (rule impI)
                    apply (drule IHs)
                    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1])
                      apply assumption+
                    apply (erule allE)
                    apply (erule impE)
                     apply assumption
                    apply (rule trans)
                     apply (erule arg_cong[of _ _ "(`) _"])
                    apply (subst FVars_raw_permutes)
                      apply (rule bij_imp_bij_inv supp_inv_bound | assumption)+
                    apply (unfold image_comp inv_o_simp2 image_id)
                    apply (rule refl)
        (* ORELSE *)
                   apply (rule ballI, rule ballI, rule imp_refl)+
        (* END REPEAT_DETERM *)
                 apply (rule supp_id_bound bij_id | assumption)+
        (* repeated *)
       apply (rule sym)
       apply (rule trans)
        apply (rule arg_cong2[of _ _ _ _ minus, rotated])
         apply (rule trans)
          apply (erule term_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
         apply (rule sym)
         apply (erule eq_on_image)
        prefer 2
        apply (rule trans)
         apply (rule image_set_diff[OF bij_is_inj, symmetric])
         apply assumption
        apply (erule id_on_image)
       apply (unfold image_UN)[1]
       apply (rule sym)
       apply (rule rel_set_UN_D)
       apply (erule term_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF term_pre.mr_rel_mono_strong[rotated -4]])
        (* REPEAT_DETERM *)
                   apply (rule ballI, rule ballI, rule imp_refl)+
        (* ORELSE *)
                  apply (rule ballI)
                  apply (rule ballI)
                  apply (rule impI)
                  apply (drule IHs)
                  apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1])
                    apply assumption+
                  apply (erule allE)
                  apply (erule impE)
                   apply assumption
                  apply (rule trans)
                   apply (erule arg_cong[of _ _ "(`) _"])
                  apply (subst FVars_raw_permutes)
                    apply (rule bij_imp_bij_inv supp_inv_bound | assumption)+
                  apply (unfold image_comp inv_o_simp2 image_id)
                  apply (rule refl)
        (* ORELSE *)
                 apply (rule ballI, rule ballI, rule imp_refl)+
        (* END REPEAT_DETERM *)
                apply (rule supp_id_bound bij_id | assumption)+
        (* repeated, rec free case *)
      apply (rule rel_set_UN_D)
      apply (erule term_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF term_pre.mr_rel_mono_strong[rotated -4]])
                  apply (rule ballI, rule ballI, rule imp_refl)+
        (* ORELSE *)
                apply (rule ballI)
                apply (rule ballI)
                apply (rule impI)
                apply (drule IHs)
                apply (erule allE)
                apply (erule impE)
                 apply assumption
                apply assumption
        (* END REPEAT_DETERM *)
               apply (rule supp_id_bound bij_id | assumption)+
      done
    done

  show "alpha_term x y \<Longrightarrow> FVars_raw_term x = FVars_raw_term y" by (erule x[THEN spec, THEN mp])
qed

lemma alpha_syms:
  fixes x::"'a::var_term_pre raw_term"
  shows "alpha_term x y \<Longrightarrow> alpha_term y x"
apply (erule alpha_term.coinduct)
  apply (erule alpha_term.cases)
  apply hypsubst

  apply (unfold triv_forall_equality)
  apply (rule exI)+
  apply (rule conjI, rule refl)+
  apply (rule conjI[rotated])+
            apply (rule iffD1[OF term_pre.mr_rel_flip, rotated -1])
                  apply (unfold inv_id)
                  apply (erule term_pre.mr_rel_mono_strong0[rotated -7])
                      apply (rule ballI, rule refl)+
                      apply (rule ballI, rule inv_inv_eq[THEN fun_cong, symmetric], assumption)+
(* REPEAT_DETERM *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (assumption | (erule alpha_bij_eq_invs[THEN iffD1, rotated -1], assumption+))
      (* repeated *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (assumption | (erule alpha_bij_eq_invs[THEN iffD1, rotated -1], assumption+))
      (* repeated *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (assumption | (erule alpha_bij_eq_invs[THEN iffD1, rotated -1], assumption+))
      (* END REPEAT_DETERM *)
                      apply (unfold inv_inv_eq)
                      apply (assumption | rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound)+

           apply (rule iffD2[OF arg_cong[of _ _ eq_on, THEN fun_cong, THEN fun_cong]])
            apply (erule term_pre.mr_rel_set[rotated -1])
             apply (rule supp_id_bound | assumption)+
           apply (rule eq_on_inv2)
          apply assumption+

          apply (rule id_on_inv)
        apply assumption+
       apply (rule id_on_antimono)
        apply assumption
       apply (rule equalityD1)
       apply (rule trans)
        apply (rule arg_cong2[of _ _ _ _ minus, rotated])
         apply (rule trans)
          apply (erule term_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
         apply (rule sym)
         apply (erule eq_on_image)
        prefer 2
        apply (rule trans)
         apply (rule image_set_diff[OF bij_is_inj, symmetric])
         apply assumption
        apply (erule id_on_image)
       apply (unfold image_UN)[1]
       apply (rule sym)
       apply (rule rel_set_UN_D)
       apply (erule term_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF term_pre.mr_rel_mono_strong[rotated -4]])
        (* REPEAT_DETERM *)
                   apply (rule ballI, rule ballI, rule imp_refl)+
        (* ORELSE *)
                  apply (rule ballI)
                  apply (rule ballI)
                  apply (rule impI)
                  apply (drule alpha_FVars)
                  apply (erule trans[rotated])
                  apply (rule sym)
                  apply (rule FVars_raw_permutes)
                   apply assumption+
            (* ORELSE *)
                   apply (rule ballI, rule ballI, rule imp_refl)+
        (* END REPEAT_DETERM *)
                apply (rule supp_id_bound bij_id supp_inv_bound bij_imp_bij_inv | assumption)+

  apply (rule id_on_inv)
        apply assumption+
       apply (rule id_on_antimono)
        apply assumption
       apply (rule equalityD1)
       apply (rule trans)
     apply (rule arg_cong2[of _ _ _ _ minus, rotated])
       apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
       apply (erule term_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
     prefer 2
      apply (unfold image_Un[symmetric])[1]
        apply (rule trans)
         apply (rule image_set_diff[OF bij_is_inj, symmetric])
         apply assumption
        apply (erule id_on_image)
       apply (unfold image_UN)[1]
       apply (rule sym)
       apply (rule rel_set_UN_D)
       apply (erule term_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF term_pre.mr_rel_mono_strong[rotated -4]])
        (* REPEAT_DETERM *)
                  apply (rule ballI)
                  apply (rule ballI)
                  apply (rule impI)
                  apply (drule alpha_FVars)
                  apply (erule trans[rotated])
                  apply (rule sym)
                  apply (rule FVars_raw_permutes)
                   apply assumption+
            (* ORELSE *)
                   apply (rule ballI, rule ballI, rule imp_refl)+
        (* END REPEAT_DETERM *)
                apply (rule supp_id_bound bij_id supp_inv_bound bij_imp_bij_inv | assumption)+
  done

lemma alpha_trans: "alpha_term x y \<Longrightarrow> alpha_term y z \<Longrightarrow> alpha_term x z"
proof -
  have x: "(\<exists>y. alpha_term x y \<and> alpha_term y z) \<Longrightarrow> alpha_term x z"
    apply (erule alpha_term.coinduct)
    apply (erule exE conjE alpha_term.cases)+
    apply hypsubst
    apply (drule iffD1[OF raw_term.inject])
    apply hypsubst
    apply (frule term_pre.mr_rel_OO[THEN fun_cong, THEN fun_cong, THEN iffD2, rotated -1, OF relcomppI])
               apply assumption
              apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold id_o o_id)

    apply (unfold triv_forall_equality)
    subgoal for g x f2 g' y f2' z
      apply (rule exI[of _ "g' \<circ> g"])
      apply (rule exI)
      apply (rule exI[of _ "f2' \<circ> f2"])
      apply (rule exI)
      apply (rule conjI, rule refl)+
      apply (rule conjI, (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+)+

      apply (rule conjI)
       apply (rule id_on_comp[rotated])
        apply assumption
       apply (erule id_on_antimono)
       apply (rule equalityD2)
       apply (rule trans)
        apply (rule arg_cong2[of _ _ _ _ minus, rotated])
        apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
         apply (erule term_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
        prefer 2
        apply (unfold image_Un[symmetric])
        apply (rule trans)
         apply (rule image_set_diff[symmetric, OF bij_is_inj])
         apply assumption
        apply (erule id_on_image)
       apply (unfold image_UN)
      apply (rule sym)
       apply (rule rel_set_UN_D)
       apply (erule term_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF term_pre.mr_rel_mono_strong[rotated -4]])
        (* REPEAT_DETERM *)
                   apply (rule ballI)
                   apply (rule ballI)
                   apply (rule impI)
                   apply (drule alpha_FVars)
                   apply (erule trans[rotated])
                   apply (rule sym)
                   apply (rule FVars_raw_permutes)
                    apply assumption+
            (* ORELSE *)
                  apply (rule ballI, rule ballI, rule imp_refl)+
        (* END REPEAT_DETERM *)
                apply (rule supp_id_bound bij_id | assumption)+

      apply (rule conjI, (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+)+

            apply (rule conjI)
       apply (rule id_on_comp[rotated])
        apply assumption
       apply (erule id_on_antimono)
       apply (rule equalityD2)
       apply (rule trans)
        apply (rule arg_cong2[of _ _ _ _ minus, rotated])
        apply (rule trans)
         apply (erule term_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
        apply (rule sym)
         apply (erule eq_on_image)
        prefer 2
        apply (rule trans)
         apply (rule image_set_diff[symmetric, OF bij_is_inj])
         apply assumption
        apply (erule id_on_image)
       apply (unfold image_UN)
      apply (rule sym)
       apply (rule rel_set_UN_D)
       apply (erule term_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF term_pre.mr_rel_mono_strong[rotated -4]])
        (* REPEAT_DETERM *)
                   apply (rule ballI, rule ballI, rule imp_refl)+
        (* ORELSE *)
                   apply (rule ballI)
                   apply (rule ballI)
                   apply (rule impI)
                   apply (drule alpha_FVars)
                   apply (erule trans[rotated])
                   apply (rule sym)
                   apply (rule FVars_raw_permutes)
                    apply assumption+
            (* ORELSE *)
                  apply (rule ballI, rule ballI, rule imp_refl)+
        (* END REPEAT_DETERM *)
                apply (rule supp_id_bound bij_id | assumption)+

      apply (rule conjI)
       apply (rule eq_on_comp)
        apply (erule eq_on_mono[rotated])
        apply (rule equalityD1)
        apply (rule trans)
         apply (erule eq_on_image)
        apply (rule sym)
         apply (erule term_pre.mr_rel_set[rotated -1], (rule supp_id_bound | assumption)+)+

      apply (erule term_pre.mr_rel_mono_strong[rotated -4])
    (* REPEAT_DETERM *)
                     apply (rule ballI)
                     apply (rule ballI)
                     apply (rule impI)
                     apply (rule disjI1)
                     apply (erule relcomppE)
                     apply (rule exI)
                     apply (rule conjI[rotated])
              apply assumption
             apply (subst permute_raw_comps[symmetric])
                 apply assumption+
             apply (rule iffD2[OF alpha_bij_eqs])
               apply assumption+
      (* repeated *)
                     apply (rule ballI)
                     apply (rule ballI)
                     apply (rule impI)
                     apply (rule disjI1)
                     apply (erule relcomppE)
                     apply (rule exI)
                     apply (rule conjI[rotated])
              apply assumption
             apply (subst permute_raw_comps[symmetric])
                 apply assumption+
             apply (rule iffD2[OF alpha_bij_eqs])
               apply assumption+
      (* repeated, free rec case *)
      apply (rule ballI)
           apply (rule ballI)
           apply (rule impI)
           apply (erule relcomppE)
           apply (rule disjI1)
           apply (rule exI)
           apply (rule conjI)
            apply assumption+
      (* END REPEAT_DETERM *)
          apply (rule supp_id_bound bij_comp supp_comp_bound infinite_UNIV | assumption)+
      done
    done

  show "alpha_term x y \<Longrightarrow> alpha_term y z \<Longrightarrow> alpha_term x z"
    apply (rule x)
    apply (rule exI)
    apply (rule conjI)
     apply assumption+
    done
qed

lemma raw_refreshs:
  fixes x::"('a::var_term_pre, 'a, 'a, 'a raw_term, 'a raw_term, 'a raw_term) term_pre"
  assumes "|A| <o |UNIV::'a set|"
  shows "\<exists>y. (set2_term_pre y \<union> set3_term_pre y) \<inter> A = {} \<and> alpha_term (raw_term_ctor x) (raw_term_ctor y)"

  apply (rule exE[OF eextend_fresh[of "set2_term_pre x \<union> set3_term_pre x"
    "(A \<union> (set2_term_pre x \<union> set3_term_pre x)) \<union> ((\<Union>(FVars_raw_term ` set4_term_pre x) \<union> \<Union>(FVars_raw_term ` set5_term_pre x)) - (set2_term_pre x \<union> set3_term_pre x))"
    "(\<Union>(FVars_raw_term ` set4_term_pre x) \<union> \<Union>(FVars_raw_term ` set5_term_pre x)) - (set2_term_pre x \<union> set3_term_pre x)"
  ]])
       apply (rule var_term_pre_class.Un_bound term_pre.set_bd_UNIV assms ordLeq_ordLess_trans[OF card_of_diff]
        term_pre.set_bd[THEN ordLess_ordLeq_trans] var_term_pre_class.UN_bound var_term_pre_class.large FVars_raw_bd_UNIVs infinite_UNIV
      )+
    apply (rule Un_upper2)
   apply (rule Diff_disjoint)
  apply (erule conjE)+
  apply (unfold Un_Diff)

  subgoal for g
    apply (rule exE[OF extend_id_on[of g "\<Union> (FVars_raw_term ` set5_term_pre x)" "set2_term_pre x \<union> set3_term_pre x" "set3_term_pre x"]])
          apply assumption+
        apply (erule id_on_antimono)
        apply (rule Un_upper2)
       apply assumption
      apply (erule Int_subset_empty2)
      apply (rule subset_trans[rotated])
       apply (rule Un_upper1)
      apply (rule Un_upper2)

     apply (rule subsetI)
     apply (rotate_tac -1)
     apply (erule contrapos_pp)
     apply (unfold Un_iff de_Morgan_disj)[1]
     apply (erule conjE)+
     apply assumption
    apply (erule conjE)+

    subgoal for f2
      apply (rule exI[of _ "map_term_pre id g g (permute_raw_term g) (permute_raw_term f2) id x"])
      apply (subst term_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
      apply (unfold image_Un[symmetric])
      apply (rule conjI)
       apply (erule Int_subset_empty2)
       apply (unfold Un_assoc)[1]
       apply (rule Un_upper1)
      apply (rule alpha_term.intros[rotated -1])
                apply (rule iffD2[OF term_pre.mr_rel_map(3), rotated -1])
                          apply (unfold inv_id id_o Grp_UNIV_id conversep_eq OO_eq)
                          apply (subst inv_o_simp1, assumption)+
                          apply (unfold term_pre.mr_rel_id[symmetric] relcompp_conversep_Grp)
                          apply (rule term_pre.rel_refl_strong)
                          apply (rule alpha_refls)+
                          apply (rule supp_id_bound bij_id | assumption)+

           apply (erule id_on_antimono)
           apply (rule Un_upper1)
         apply assumption+
      done
    done
  done

lemma avoid_raw_freshs:
  fixes x::"'a::var_term_pre raw_term_pre"
  assumes "|A| <o |UNIV::'a set|"
shows "set2_term_pre (avoid_raw_term x A) \<inter> A = {}" "set3_term_pre (avoid_raw_term x A) \<inter> A = {}"
   apply (unfold avoid_raw_term_def)
  (* REPEAT_DETERM *)
   apply (rule someI2_ex)
    apply (rule raw_refreshs[OF assms])
  apply (unfold Int_Un_distrib2 Un_empty)[1]
   apply (erule conjE)+
   apply assumption
  (* repeated *)
   apply (rule someI2_ex)
    apply (rule raw_refreshs[OF assms])
  apply (unfold Int_Un_distrib2 Un_empty)[1]
   apply (erule conjE)+
   apply assumption
  (* END REPEAT_DETERM *)
  done

lemma TT_Quotients: "Quotient alpha_term TT_abs TT_rep (\<lambda>x. (=) (TT_abs x))"
  apply (subgoal_tac "Quotient3 alpha_term TT_abs TT_rep")
   prefer 2
   apply (rule quot_type.Quotient)
   apply (rule type_definition_quot_type)
    apply (rule type_definition_term)
   apply (rule equivpI)
     apply (rule reflpI)
     apply (rule alpha_refls)
    apply (rule sympI)
    apply (erule alpha_syms)
   apply (rule transpI)
   apply (erule alpha_trans)
   apply assumption
  apply (rule QuotientI)
     apply (erule Quotient3_abs_rep)
    apply (rule alpha_refls)
   apply (erule Quotient3_rel[symmetric])
  apply (rule ext)+
  apply (rule iffI)
   apply (rule conjI)
    apply (rule alpha_refls)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

lemmas TT_total_abs_eq_iffs = TT_Quotients[THEN Quotient_total_abs_eq_iff, OF reflpI[OF alpha_refls]]
lemmas TT_rep_abs = TT_Quotients[THEN Quotient_rep_abs, OF alpha_refls]
lemmas TT_abs_rep = TT_Quotients[THEN Quotient_abs_rep]

lemmas TT_rep_abs_syms = alpha_syms[OF TT_rep_abs]

lemma TT_abs_ctors: "TT_abs (raw_term_ctor x) = term_ctor (map_term_pre id id id TT_abs TT_abs TT_abs x)"
  apply (unfold term_ctor_def)
  apply (rule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule alpha_term.intros)
         apply (rule supp_id_bound bij_id id_on_id eq_on_refl)+
  apply (unfold permute_raw_ids term_pre.mr_rel_id[symmetric])
  apply (subst term_pre.map_comp)
    apply (rule supp_id_bound bij_id)+
  apply (unfold id_o o_id)
  apply (rule iffD2[OF term_pre.rel_map(2)])
  apply (unfold comp_def)
  apply (rule term_pre.rel_refl_strong)
    apply (rule TT_rep_abs_syms)+
  done

lemma permute_simps:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "permute_term f (term_ctor x) = term_ctor (map_term_pre f f f (permute_term f) (permute_term f) (permute_term f) x)"
  apply (unfold term_ctor_def permute_term_def)
  apply (subst term_pre.map_comp)
      apply (rule supp_id_bound bij_id assms)+
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (rule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule alpha_bij_eq_invs[OF assms, THEN iffD2])
  apply (subst permute_raw_simps)
    apply (rule bij_imp_bij_inv supp_inv_bound assms)+
  apply (subst term_pre.map_comp)
      apply (rule bij_imp_bij_inv supp_inv_bound assms)+
  apply (subst inv_o_simp1, rule assms)+
  apply (rule alpha_trans)
  apply (rule TT_rep_abs)
  apply (unfold comp_def)
  apply (rule alpha_term.intros)
         apply (rule bij_id supp_id_bound id_on_id eq_on_refl)+
  apply (rule iffD2[OF term_pre.mr_rel_id[symmetric, THEN fun_cong, THEN fun_cong]])
  apply (rule iffD2[OF term_pre.rel_map(1)])
  apply (rule iffD2[OF term_pre.rel_map(2)])
  apply (unfold permute_raw_ids)
  apply (rule term_pre.rel_refl_strong)
  (* REPEAT_DETERM *)
    apply (rule alpha_bij_eq_invs[THEN iffD1])
      apply (rule assms supp_id_bound bij_id)+
    apply (rule TT_rep_abs_syms)
  (* repeated *)
    apply (rule alpha_bij_eq_invs[THEN iffD1])
      apply (rule assms supp_id_bound bij_id)+
    apply (rule TT_rep_abs_syms)
  (* repeated *)
    apply (rule alpha_bij_eq_invs[THEN iffD1])
      apply (rule assms supp_id_bound bij_id)+
    apply (rule TT_rep_abs_syms)
  (* END REPEAT_DETERM *)
  done

lemma permute_ids: "permute_term id x = x"
  apply (unfold permute_term_def permute_raw_ids TT_abs_rep)
  apply (rule refl)
  done

lemmas permute_id0s = permute_ids[THEN trans[OF _ id_apply[symmetric]], abs_def, THEN meta_eq_to_obj_eq]

lemma permute_comps:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "permute_term g (permute_term f x) = permute_term (g \<circ> f) x"
  apply (unfold permute_term_def)
  apply (subst permute_raw_comps[symmetric])
      apply (rule assms)+
  apply (rule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule alpha_bij_eqs[THEN iffD2])
    apply (rule assms)+
  apply (rule TT_rep_abs)
  done

lemma permute_comp0s:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "permute_term g \<circ> permute_term f = permute_term (g \<circ> f)"
  apply (rule ext)
  apply (rule trans[OF comp_apply])
  apply (rule permute_comps[OF assms])
  done

lemma permute_bijs:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "bij (permute_term f)"
  apply (rule o_bij)
   apply (rule trans)
    apply (rule permute_comp0s)
       prefer 5 (* 4 * nvars + 1 *)
       apply (subst inv_o_simp1, rule assms)+
       apply (rule permute_id0s)
      apply (rule bij_imp_bij_inv supp_inv_bound assms)+
  apply (rule trans)
   apply (rule permute_comp0s)
      apply (rule bij_imp_bij_inv supp_inv_bound assms)+
  apply (subst inv_o_simp2, rule assms)+
  apply (rule permute_id0s)
  done

lemma permute_inv_simps:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "inv (permute_term f) = permute_term (inv f)"
  apply (rule inv_unique_comp)
  (* REPEAT_DETERM *)
   apply (rule trans)
    apply (rule permute_comp0s)
       apply (rule bij_imp_bij_inv supp_inv_bound assms)+
   apply (subst inv_o_simp1 inv_o_simp2, rule assms)+
   apply (rule permute_id0s)
  (* repeated *)
   apply (rule trans)
    apply (rule permute_comp0s)
       apply (rule bij_imp_bij_inv supp_inv_bound assms)+
   apply (subst inv_o_simp1 inv_o_simp2, rule assms)+
  apply (rule permute_id0s)
  done

lemma FVars_bds: "|FVars_term x| <o natLeq"
  apply (unfold FVars_term_def)
  apply (rule FVars_raw_bds)
  done

lemmas FVars_bd_UNIVs = ordLess_ordLeq_trans[OF FVars_bds var_term_pre_class.large]

lemma FVars_permutes:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "FVars_term (permute_term f x) = f ` FVars_term x"
  apply (unfold FVars_term_def permute_term_def)
  apply (rule trans)
   apply (rule alpha_FVars)
   apply (rule TT_rep_abs)
  apply (rule FVars_raw_permutes[OF assms])
  done

lemma FVars_ctors:
  "FVars_term (term_ctor x) = set1_term_pre x \<union> (\<Union>(FVars_term ` set4_term_pre x) - (set2_term_pre x \<union> set3_term_pre x))
   \<union> (\<Union>(FVars_term ` set5_term_pre x) - set3_term_pre x) \<union> \<Union>(FVars_term ` set6_term_pre x)"
  apply (unfold FVars_term_def term_ctor_def)
  apply (rule trans)
   apply (rule alpha_FVars)
   apply (rule TT_rep_abs)
  apply (rule trans)
   apply (rule FVars_raw_ctors)
  apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def])
  apply (rule refl)
  done

lemma FVars_intros:
  "a \<in> set1_term_pre x \<Longrightarrow> a \<in> FVars_term (term_ctor x)"
  "z \<in> set4_term_pre x \<Longrightarrow> a \<in> FVars_term z \<Longrightarrow> a \<notin> set2_term_pre x \<union> set3_term_pre x \<Longrightarrow> a \<in> FVars_term (term_ctor x)"
  "z \<in> set5_term_pre x \<Longrightarrow> a \<in> FVars_term z \<Longrightarrow> a \<notin> set3_term_pre x \<Longrightarrow> a \<in> FVars_term (term_ctor x)"
  "z \<in> set6_term_pre x \<Longrightarrow> a \<in> FVars_term z \<Longrightarrow> a \<in> FVars_term (term_ctor x)"
     apply (unfold FVars_term_def term_ctor_def alpha_FVars[OF TT_rep_abs])
  (* for thm in FVars_intros *)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
      prefer 2
      apply (erule FVars_raw_intros(1)[rotated])
     apply (subst term_pre.set_map)
       apply (rule supp_id_bound bij_id)+
     apply (unfold image_id)?
     apply assumption?
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)?
     apply (erule imageI)?
     apply (rule refl)
  (* repeated *)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
      prefer 2
      apply (erule FVars_raw_intros(2)[rotated])
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
     apply (unfold image_id)?
     apply assumption?
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)?
     apply (erule imageI)?
     apply (rule refl)
  (* repeated *)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
      prefer 2
      apply (erule FVars_raw_intros(3)[rotated])
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
     apply (unfold image_id)?
     apply assumption?
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)?
     apply (erule imageI)?
     apply (rule refl)
  (* repeated *)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
      prefer 2
      apply (erule FVars_raw_intros(4)[rotated])
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
     apply (unfold image_id)?
     apply assumption?
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)?
     apply (erule imageI)?
     apply (rule refl)
  (* END REPEAT_DETERM *)
  done

lemma TT_inject0s:
  "(term_ctor x = term_ctor y) \<longleftrightarrow> (\<exists>(g::'a::var_term_pre \<Rightarrow> 'a) f2.
    bij g \<and> |supp g| <o |UNIV::'a set| \<and>
    id_on (\<Union>(FVars_term ` set4_term_pre x) - (set2_term_pre x \<union> set3_term_pre x)) g \<and>
    bij f2 \<and> |supp f2| <o |UNIV::'a set| \<and> id_on (\<Union>(FVars_term ` set5_term_pre x) - set3_term_pre x) f2 \<and>
    eq_on (set3_term_pre x) f2 g \<and>
    map_term_pre id g g (permute_term g) (permute_term f2) id x = y)"
  apply (unfold term_ctor_def permute_term_def)
  apply (rule trans)
   apply (rule TT_total_abs_eq_iffs)
  apply (rule iffI)
   apply (erule alpha_term.cases)
   apply (drule iffD1[OF raw_term.inject])+
   apply hypsubst
   apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id image_comp[unfolded comp_def])
   apply (drule iffD1[OF term_pre.mr_rel_map(1), rotated -1])
             apply (rule supp_id_bound bij_id | assumption)+
   apply (unfold id_o o_id)
   apply (drule iffD1[OF term_pre.mr_rel_map(3), rotated -1])
              apply (rule supp_id_bound bij_id | assumption)+
   apply (unfold inv_id id_o o_id relcompp_conversep_Grp)
   apply (unfold Grp_OO FVars_term_def[symmetric])
   apply (rule exI)+
   apply (rule conjI[rotated])+
          apply (rule term_pre.mr_rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD1])
          apply (rule iffD2[OF term_pre.mr_rel_map(1), rotated -1])
                    apply (unfold id_o o_id Grp_OO)
                    apply (erule term_pre.mr_rel_mono_strong[rotated -4])
            (* REPEAT_DETERM *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply assumption
            (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply assumption
            (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply hypsubst
                      apply (rule id_apply)
            (* END REPEAT_DETERM *)
                      apply (rule supp_id_bound bij_id | assumption)+

  apply (erule exE conjE)+
  apply hypsubst_thin
  apply (subst term_pre.map_comp)
      apply (rule supp_id_bound bij_id | assumption)+
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (rule alpha_term.intros[rotated -1])
         apply (rule iffD2[OF term_pre.mr_rel_map(1), rotated -1])
                   apply (unfold id_o o_id Grp_UNIV_id eq_OO)
                   apply (rule iffD2[OF term_pre.mr_rel_map(3), rotated -1])
                      apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq eq_OO)
                      apply (unfold relcompp_conversep_Grp Grp_OO)
                      apply (subst inv_o_simp1, assumption)+
                      apply (rule iffD1[OF term_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
                      apply (rule term_pre.rel_refl_strong)
                      apply (rule alpha_refls TT_rep_abs_syms)+
                      apply (rule supp_id_bound bij_id | assumption)+
              (* REPEAT_DETERM *)
      apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
      apply (unfold image_id FVars_term_def image_comp[unfolded comp_def])
      apply assumption+
      (* repeated *)
      apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
      apply (unfold image_id FVars_term_def image_comp[unfolded comp_def])
      apply assumption+
      (* repeated *)
      apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
      apply (unfold image_id FVars_term_def image_comp[unfolded comp_def])
      apply assumption+
      (* END REPEAT_DETERM *)
  done

lemma avoid_freshs:
  fixes x::"'a::var_term_pre term_pre'"
  assumes "|A| <o |UNIV::'a set|"
  shows "set2_term_pre (avoid_term x A) \<inter> A = {}" "set3_term_pre (avoid_term x A) \<inter> A = {}"
   apply (unfold avoid_term_def)
  (* REPEAT_DETERM *)
   apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)
   apply (rule avoid_raw_freshs[OF assms])
   (* repeated *)
   apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)
   apply (rule avoid_raw_freshs[OF assms])
   (* END REPEAT_DETERM *)
  done

lemma alpha_avoids:
  fixes x::"'a::var_term_pre term_pre'"
  assumes "|A| <o |UNIV::'a set|"
  shows "term_ctor (avoid_term x A) = term_ctor x"
  apply (unfold avoid_term_def avoid_raw_term_def)
  apply (rule someI2_ex)
   apply (rule raw_refreshs[OF assms])
  apply (erule conjE)+
  apply (unfold term_ctor_def)
  apply (subst term_pre.map_comp)
    apply (rule supp_id_bound bij_id)+
  apply (unfold id_o o_id)
  apply (drule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule trans[rotated])
   apply (erule sym)
  apply (rule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule alpha_term.intros)
         apply (rule supp_id_bound bij_id id_on_id eq_on_refl)+
  apply (rule iffD2[OF term_pre.mr_rel_map(1), rotated -1])
            apply (unfold id_o o_id Grp_OO permute_raw_ids)
            apply (unfold comp_def term_pre.mr_rel_id[symmetric])
            apply (rule term_pre.rel_refl_strong)
              apply (rule TT_rep_abs)+
           apply (rule supp_id_bound bij_id)+
  done

lemma fresh_cases:
  fixes y::"'a::var_term_pre term"
  assumes "|A| <o |UNIV::'a set|"
  and "\<And>(x::'a term_pre'). y = term_ctor x \<Longrightarrow> set2_term_pre x \<inter> A = {} \<Longrightarrow> set3_term_pre x \<inter> A = {} \<Longrightarrow> P"
shows P
  apply (rule raw_term.exhaust[of "TT_rep y"])
  apply (rule assms)
    defer
    apply (rule avoid_freshs[OF assms(1)])+
  apply (rule trans[rotated])
   apply (rule sym)
   apply (rule alpha_avoids[OF assms(1)])
  apply (unfold term_ctor_def)
  apply (rule TT_Quotients[THEN Quotient_rel_abs2])
  apply (rule arg_cong2[OF _ refl, of _ _ alpha_term, THEN iffD2])
   apply assumption
  apply (rule alpha_term.intros)
         apply (rule supp_id_bound bij_id id_on_id eq_on_refl)+
         apply (subst term_pre.map_comp)
                apply (rule supp_id_bound bij_id)+
         apply (unfold id_o o_id)
         apply (rule iffD2[OF term_pre.mr_rel_map(3), rotated -1])
                    apply (unfold inv_id id_o o_id Grp_OO relcompp_conversep_Grp)
             apply (unfold comp_def term_pre.mr_rel_id[symmetric] permute_raw_ids)
             apply (rule term_pre.rel_refl_strong)
               apply (rule TT_rep_abs_syms)+
            apply (rule supp_id_bound bij_id)+
  done

lemma alpha_subshapess: "alpha_term x y \<Longrightarrow> subshape_term_term z x \<Longrightarrow> subshape_term_term z y"
proof -
  have x: "(\<forall>x. alpha_term x y \<longrightarrow> (\<forall>z. subshape_term_term z x \<longrightarrow> subshape_term_term z y))"
    apply (rule raw_term.induct[of _ y])
    subgoal premises IHs for x
      apply (rule allI impI)+
      apply (erule alpha_term.cases)
      apply (erule subshape_term_term.cases)
      apply hypsubst
      apply (drule iffD1[OF raw_term.inject])+
      apply hypsubst
      apply (erule UnE)+
    (* REPEAT_DETERM *)
        apply (drule term_pre.mr_rel_set(4-6)[rotated -1])
              prefer 6 (* free + 2 * bound + 1 *)
              apply assumption
             apply (rule supp_id_bound bij_id | assumption)+
        apply (erule bexE)
        apply (frule IHs)
        apply (erule allE)
        apply (erule impE)
         apply assumption
        apply (rule subshape_term_term.intros[rotated -1])
           apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 3 1] 1\<close>)
          prefer 3 (* 2 * nvars + 1 *)
          apply (rule alpha_trans[rotated])
           apply assumption
          apply (rule alpha_trans[rotated])
           apply (rule alpha_bij_eqs[THEN iffD2, rotated -1])
             apply assumption+
          apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ alpha_term], rotated])
           apply (rule alpha_refls)
          apply (rule sym)
          apply (rule permute_raw_comps)
             apply assumption+
         apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
      (* repeated *)
        apply (drule term_pre.mr_rel_set(4-6)[rotated -1])
              prefer 6 (* free + 2 * bound + 1 *)
              apply assumption
             apply (rule supp_id_bound bij_id | assumption)+
        apply (erule bexE)
        apply (frule IHs)
        apply (erule allE)
        apply (erule impE)
         apply assumption
        apply (rule subshape_term_term.intros[rotated -1])
           apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
          prefer 3 (* 2 * nvars + 1 *)
          apply (rule alpha_trans[rotated])
           apply assumption
          apply (rule alpha_trans[rotated])
           apply (rule alpha_bij_eqs[THEN iffD2, rotated -1])
             apply assumption+
          apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ alpha_term], rotated])
           apply (rule alpha_refls)
          apply (rule sym)
          apply (rule permute_raw_comps)
             apply assumption+
        apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
        (* repeated *)
        apply (drule term_pre.mr_rel_set(4-6)[rotated -1])
              prefer 6 (* free + 2 * bound + 1 *)
              apply assumption
             apply (rule supp_id_bound bij_id | assumption)+
        apply (erule bexE)
        apply (frule IHs)
        apply (erule allE)
        apply (erule impE)
         apply assumption
        apply (rule subshape_term_term.intros[rotated -1])
           apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
          prefer 3 (* 2 * nvars + 1 *)
          apply (rule alpha_trans[rotated])
         apply assumption+
      (* END REPEAT_DETERM *)
      done
    done

  show "alpha_term x y \<Longrightarrow> subshape_term_term z x \<Longrightarrow> subshape_term_term z y"
    apply (erule x[THEN spec, THEN mp, THEN spec, THEN mp])
    apply assumption
    done
qed

lemma subshape_induct_raw:
  fixes x::"'a::var_term_pre raw_term"
  assumes "\<And>x. (\<And>y. subshape_term_term y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "\<forall>f y. bij f \<longrightarrow> |supp f| <o |UNIV::'a set| \<longrightarrow> alpha_term (permute_raw_term f x) y \<longrightarrow> P y"
  apply (rule raw_term.induct[of _ x])
  subgoal premises IHs for x
    apply (rule allI impI)+
    apply (rule assms)
    (* REPEAT_DETERM *)
    apply (drule alpha_subshapess[rotated -1])
     apply (erule alpha_syms)
    apply (rotate_tac -2)
    apply (erule thin_rl)
    apply (subst (asm) permute_raw_simps)
      apply assumption+
    apply (erule subshape_term_term.cases)
    apply (drule iffD1[OF raw_term.inject])
    apply hypsubst
    apply (subst (asm) term_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
    apply (unfold image_Un[symmetric])
    apply (erule imageE)
    apply hypsubst
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1])
      apply assumption+
    apply (subst (asm) permute_raw_comps)
        apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
    apply (erule UnE)+
  (* REPEAT_DETERM *)
      apply (drule IHs)
      apply (erule allE)+
    (* REPEAT_DETERM *)
      apply (erule impE) prefer 2
    apply (erule impE) prefer 2
    apply (erule impE) prefer 2
  (* END REPEAT_DETERM *)
         apply assumption
        apply (erule alpha_syms)
       apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
    (* repeated *)
      apply (drule IHs)
      apply (erule allE)+
    (* REPEAT_DETERM *)
      apply (erule impE) prefer 2
    apply (erule impE) prefer 2
    apply (erule impE) prefer 2
  (* END REPEAT_DETERM *)
         apply assumption
        apply (erule alpha_syms)
       apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
    (* repeated *)
      apply (drule IHs)
      apply (erule allE)+
    (* REPEAT_DETERM *)
      apply (erule impE) prefer 2
    apply (erule impE) prefer 2
    apply (erule impE) prefer 2
  (* END REPEAT_DETERM *)
         apply assumption
        apply (erule alpha_syms)
       apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
    (* END REPEAT_DETERM *)
    done
  done

lemma subshape_induct:
  fixes x::"'a::var_term_pre raw_term"
  assumes "\<And>x. (\<And>y. subshape_term_term y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  apply (rule subshape_induct_raw[THEN spec, THEN spec, THEN mp, THEN mp, THEN mp])
     apply (rule assms)
     apply assumption
    apply (rule bij_id supp_id_bound)+
  apply (unfold permute_raw_ids)
  apply (rule alpha_refls)
  done

lemma wf_subshape: "wf {(x, y). subshape_term_term x y }"
  apply (rule wfUNIVI)
  apply (unfold prod_in_Collect_iff prod.case)
    apply (rule subshape_induct)
    apply (erule allE)
    apply (erule impE)
    apply (rule allI)
     apply (rule impI)
     apply assumption
    apply assumption
  done

lemma set_subshapess:
  "z \<in> set4_term_pre x \<Longrightarrow> subshape_term_term z (raw_term_ctor x)"
  "z \<in> set5_term_pre x \<Longrightarrow> subshape_term_term z (raw_term_ctor x)"
  "z \<in> set6_term_pre x \<Longrightarrow> subshape_term_term z (raw_term_ctor x)"
  (* REPEAT_DETERM *)
    apply (rule subshape_term_term.intros)
       apply (rule supp_id_bound bij_id)+
     apply (unfold permute_raw_ids)
     apply (rule alpha_refls)
    apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 3 1] 1\<close>)
  (* repeated *)
    apply (rule subshape_term_term.intros)
       apply (rule supp_id_bound bij_id)+
     apply (unfold permute_raw_ids)
     apply (rule alpha_refls)
    apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
  (* repeated *)
    apply (rule subshape_term_term.intros)
       apply (rule supp_id_bound bij_id)+
     apply (unfold permute_raw_ids)
     apply (rule alpha_refls)
    apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
  (* END REPEAT_DETERM *)
  done

lemma set_subshape_permutess:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows
  "z \<in> set4_term_pre x \<Longrightarrow> subshape_term_term (permute_raw_term f z) (raw_term_ctor x)"
  "z \<in> set5_term_pre x \<Longrightarrow> subshape_term_term (permute_raw_term f z) (raw_term_ctor x)"
  "z \<in> set6_term_pre x \<Longrightarrow> subshape_term_term (permute_raw_term f z) (raw_term_ctor x)"
  (* REPEAT_DETERM *)
    apply (rule subshape_term_term.intros[rotated -2])
       apply (subst permute_raw_comps)
           prefer 5 (* 4 * nvars + 1 *)
           apply (subst inv_o_simp1, rule assms)+
           apply (unfold permute_raw_ids)
           apply (rule alpha_refls)
                     apply (rule assms bij_imp_bij_inv supp_inv_bound)+
      apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 3 1] 1\<close>)
     apply (rule assms bij_imp_bij_inv supp_inv_bound)+
      (* repeated *)
    apply (rule subshape_term_term.intros[rotated -2])
       apply (subst permute_raw_comps)
           prefer 5 (* 4 * nvars + 1 *)
           apply (subst inv_o_simp1, rule assms)+
           apply (unfold permute_raw_ids)
           apply (rule alpha_refls)
                     apply (rule assms bij_imp_bij_inv supp_inv_bound)+
      apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
     apply (rule assms bij_imp_bij_inv supp_inv_bound)+
      (* repeated *)
    apply (rule subshape_term_term.intros[rotated -2])
       apply (subst permute_raw_comps)
           prefer 5 (* 4 * nvars + 1 *)
           apply (subst inv_o_simp1, rule assms)+
           apply (unfold permute_raw_ids)
           apply (rule alpha_refls)
                     apply (rule assms bij_imp_bij_inv supp_inv_bound)+
      apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
     apply (rule assms bij_imp_bij_inv supp_inv_bound)+
      (* END REPEAT_DETERM *)
  done

lemma permute_abs:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "permute_term f (TT_abs x) = TT_abs (permute_raw_term f x)"
  apply (unfold permute_term_def)
  apply (rule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule alpha_bij_eqs[THEN iffD2, OF assms])
  apply (rule TT_rep_abs)
  done

lemma permute_congs:
  fixes f g::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "(\<And>a. a \<in> FVars_term x \<Longrightarrow> f a = g a) \<Longrightarrow> permute_term f x = permute_term g x"
  apply (unfold permute_term_def atomize_all atomize_imp eq_on_def[symmetric] FVars_term_def)
  apply (rule impI)
  apply (rule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule alpha_bijs)
       apply (rule assms)+
   apply assumption+
  apply (rule alpha_refls)
  done

lemmas permute_cong_ids = permute_congs[OF _ _ bij_id supp_id_bound, unfolded permute_ids, unfolded id_def]

lemma existential_induct:
  assumes IHs: "\<And>x \<rho>. \<rho> \<in> Param \<Longrightarrow> \<exists>y. term_ctor y = term_ctor x \<and>
    ((\<forall>z. z \<in> set4_term_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P z \<rho>)) \<and>
     (\<forall>z. z \<in> set5_term_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P z \<rho>)) \<and>
     (\<forall>z. z \<in> set6_term_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P z \<rho>)) \<longrightarrow> P (term_ctor y) \<rho>)"
  shows "\<forall>\<rho>\<in>Param. P z \<rho>"
  apply (unfold ball_conj_distrib)?
  apply (rule subshape_induct[of "\<lambda>x. \<forall>\<rho>\<in>Param. P (TT_abs x) \<rho>" "TT_rep z", unfolded TT_abs_rep])
  apply (rule ballI)
  subgoal for x \<rho>
    apply (rule raw_term.exhaust[of x])
    apply hypsubst_thin
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ P]])
     apply (rule TT_total_abs_eq_iffs[THEN iffD2])
     apply (rule alpha_term.intros)
            apply (rule bij_id supp_id_bound id_on_id eq_on_refl)+
     apply (unfold permute_raw_ids)
     apply (rule iffD2[OF term_pre.mr_rel_map(3)])
                apply (rule supp_id_bound bij_id)+
     apply (unfold inv_id id_o o_id relcompp_conversep_Grp term_pre.mr_rel_id[symmetric])
     apply (rule term_pre.rel_refl_strong)
        apply (rule TT_rep_abs_syms[unfolded comp_apply[symmetric, of TT_rep TT_abs]])+
    apply (unfold id_hid_o_hid)
    apply (unfold hidden_id_def)
    apply (subst term_pre.map_comp[symmetric])
      apply (rule supp_id_bound bij_id)+
    apply (unfold term_ctor_def[symmetric])
    apply (drule IHs)
    apply (erule exE)
    apply (erule conjE)
    apply (drule sym)
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ P]])
    apply assumption
    apply (erule mp)
     apply (drule TT_inject0s[THEN iffD1])
    apply (erule exE conjE)+
    apply hypsubst
    apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (subst term_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
    apply (unfold image_comp[unfolded comp_def] image_id)
    (* REPEAT_DETERM *)
    apply (rule conjI)?
     apply (rule allI)
     apply (rule impI)
     apply (erule imageE)
     apply hypsubst
     apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
     apply (drule set_subshapess set_subshape_permutess[rotated -1], assumption)
      apply assumption+
    (* repeated *)
    apply (rule conjI)?
     apply (rule allI)
     apply (rule impI)
     apply (erule imageE)
     apply hypsubst
          apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
     apply (drule set_subshape_permutess[rotated -1])
    prefer 3 (* 2 * nvars + 1 *)
      apply assumption+
    (* repeated *)
    apply (rule conjI)?
     apply (rule allI)
     apply (rule impI)
     apply (erule imageE)
     apply hypsubst
    apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold id_def)[1]
    apply (drule set_subshapess, assumption)
    (* END REPEAT_DETERM *)
    done
  done

lemma fresh_induct_param:
  fixes K::"'p \<Rightarrow> 'a::var_term_pre set"
  assumes "\<And>\<rho>. \<rho> \<in> Param \<Longrightarrow> |K \<rho>| <o |UNIV::'a set|"
  and IHs: "\<And>x \<rho>.
    (\<And>z \<rho>. z \<in> set4_term_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P z \<rho>) \<Longrightarrow>
    (\<And>z \<rho>. z \<in> set5_term_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P z \<rho>) \<Longrightarrow>
    (\<And>z \<rho>. z \<in> set6_term_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P z \<rho>) \<Longrightarrow>
    set2_term_pre x \<inter> K \<rho> = {} \<Longrightarrow> set3_term_pre x \<inter> K \<rho> = {} \<Longrightarrow>
    \<rho> \<in> Param \<Longrightarrow> P (term_ctor x) \<rho>"
shows "\<forall>\<rho>\<in>Param. P z \<rho>"
  apply (rule existential_induct[of _ P z])
  subgoal for x \<rho>
    apply (rule fresh_cases[of "K \<rho>" "term_ctor x"])
     apply (erule assms)
    apply (rule exI)
    apply (rule conjI)
     apply (erule sym)
    apply (rule impI)
    apply (erule conjE)+
    apply (rule IHs)
    (* for i in [~rec_vars - 2 .. ~3] *)
        apply (rotate_tac -5)
        apply (erule allE)
        apply (erule impE)
         apply assumption
        apply (erule ballE)
         apply assumption
        apply (rotate_tac -1)
        apply (erule contrapos_np)
        apply assumption
    (* repeated *)
        apply (rotate_tac -4)
        apply (erule allE)
        apply (erule impE)
         apply assumption
        apply (erule ballE)
         apply assumption
        apply (rotate_tac -1)
        apply (erule contrapos_np)
        apply assumption
    (* repeated *)
        apply (rotate_tac -3)
        apply (erule allE)
        apply (erule impE)
         apply assumption
        apply (erule ballE)
         apply assumption
        apply (rotate_tac -1)
        apply (erule contrapos_np)
        apply assumption
    (* END REPEAT_DETERM *)
      apply assumption+
    done
  done

lemma nnoclash_noclashs:
  "noclash_term x = noclash_raw_term (map_term_pre id id id TT_rep TT_rep TT_rep x)"
  apply (unfold noclash_term_def noclash_raw_term_def)
  apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def] FVars_term_def[symmetric])
  apply (rule refl)
  done

end