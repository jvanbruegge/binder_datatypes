theory STLC
  imports "thys/MRBNF_Recursor"
begin

(* TODO: Move into MRBNF_Recursor.thy *)
ML_file \<open>./Tools/mrbnf_recursor_tactics.ML\<close>
ML_file \<open>./Tools/mrbnf_recursor.ML\<close>

ML_file \<open>./Tools/mrbnf_vvsubst_tactics.ML\<close>
ML_file \<open>./Tools/mrbnf_vvsubst.ML\<close>

datatype \<tau> = Unit | Arrow \<tau> \<tau> (infixr "\<rightarrow>" 40)

(* binder_datatype 'a terms =
  Var 'a
| App "'a terms" "'a terms"
| Abs x::'a \<tau> t::"'a terms" binds x in t
*)

ML \<open>
val name = "terms"
val T = @{typ "'var + 'rec * 'rec + 'bvar * \<tau> * 'brec"}

structure Data = Generic_Data (
  type T = MRBNF_FP_Def_Sugar.fp_result list Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
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

  (* Step 4.5: Save fp_result for later use *)
  val lthy = Local_Theory.declaration {syntax=false, pervasive=true}
    (fn phi => Data.map (Symtab.update (name, map (MRBNF_FP_Def_Sugar.morph_fp_result phi) res))) lthy

  (* Step 5: Create recursor and create fixpoint as MRBNF *)
  val (rec_mrbnf, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint @{binding vvsubst} I (hd res) lthy;

  (* Step 6: Register fixpoint MRBNF *)
  val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (#quotient_fp (hd res))))) rec_mrbnf lthy;
in lthy end
\<close>
print_theorems
print_mrbnfs

lemma UN_single: "\<Union>(f ` {a}) = f a" by simp

definition Var :: "'a::var_terms_pre \<Rightarrow> 'a terms" where
  "Var a \<equiv> terms_ctor (Abs_terms_pre (Inl a))"
definition App :: "'a::var_terms_pre terms \<Rightarrow> 'a terms \<Rightarrow> 'a terms" where
  "App e1 e2 \<equiv> terms_ctor (Abs_terms_pre (Inr (Inl (e1, e2))))"
definition Abs :: "'a::var_terms_pre \<Rightarrow> \<tau> \<Rightarrow> 'a terms \<Rightarrow> 'a terms" where
  "Abs x t e \<equiv> terms_ctor (Abs_terms_pre (Inr (Inr (x, t, e))))"

lemma FFVars_terms_simps[simp]:
  "FFVars_terms (Var a) = {a}"
  "FFVars_terms (App e1 e2) = FFVars_terms e1 \<union> FFVars_terms e2"
  "FFVars_terms (Abs x \<tau> e) = FFVars_terms e - {x}"
  unfolding Var_def App_def Abs_def terms.FFVars_cctors set1_terms_pre_def set2_terms_pre_def set3_terms_pre_def set4_terms_pre_def
    Abs_terms_pre_inverse[OF UNIV_I] comp_def map_sum_def sum.case sum_set_simps Union_empty UN_empty
    Un_empty_left Un_empty_right cSup_singleton empty_Diff map_prod_def prod.case prod_set_simps
    image_Un Union_Un_distrib UN_single
  apply (rule refl)+
  done

lemma rrename_simps:
  assumes "bij (f::'a::var_terms_pre \<Rightarrow> 'a)" "|supp f| <o |UNIV::'a set|"
  shows "rrename_terms f (Var a) = Var (f a)"
    "rrename_terms f (App e1 e2) = App (rrename_terms f e1) (rrename_terms f e2)"
    "rrename_terms f (Abs x \<tau> e) = Abs (f x) \<tau> (rrename_terms f e)"
  unfolding Var_def App_def Abs_def terms.rrename_cctors[OF assms] map_terms_pre_def comp_def
    Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case map_prod_def prod.case id_def
    apply (rule refl)+
  done

lemma App_inject[simp]: "(App a b = App c d) = (a = c \<and> b = d)"
proof
  assume "App a b = App c d"
  then show "a = c \<and> b = d"
    unfolding App_def fun_eq_iff terms.TT_injects0
      map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
      Abs_terms_pre_inject[OF UNIV_I UNIV_I]
    by blast
qed simp
lemma Var_inject[simp]: "(Var a = Var b) = (a = b)"
  apply (rule iffI[rotated])
   apply (rule arg_cong[of _ _ Var])
  apply assumption
  unfolding Var_def terms.TT_injects0 map_terms_pre_def comp_def map_sum_def sum.case Abs_terms_pre_inverse[OF UNIV_I]
  id_def Abs_terms_pre_inject[OF UNIV_I UNIV_I] sum.inject
  apply (erule exE conjE)+
  apply assumption
  done
lemma Abs_inject: "(Abs x \<tau> e = Abs x' \<tau>' e') = (\<exists>f. bij f \<and> |supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<and> id_on (FFVars_terms (Abs x \<tau> e)) f \<and> f x = x' \<and> \<tau> = \<tau>' \<and> rrename_terms f e = e')"
  unfolding FFVars_terms_simps
  unfolding Abs_def terms.TT_injects0 map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_terms_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_terms_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_terms_pre_def
    Un_empty_right UN_single
  apply (rule refl)
  done

lemma terms_distinct[simp]:
  "Var a \<noteq> App e1 e2"
  "Var a \<noteq> Abs x \<tau> e"
  "App e1 e2 \<noteq> Var a"
  "App e1 e2 \<noteq> Abs x \<tau> e"
  "Abs x \<tau> e \<noteq> Var a"
  "Abs x \<tau> e \<noteq> App e1 e2"
  unfolding Var_def App_def Abs_def terms.TT_injects0 map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I]
    Abs_terms_pre_inject[OF UNIV_I UNIV_I] map_sum_def sum.case
  by auto

lemma bij_map_terms_pre: "bij f \<Longrightarrow> |supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij (map_terms_pre (id::_::var_terms_pre \<Rightarrow> _) f (rrename_terms f) id)"
  apply (rule iffD2[OF bij_iff])
    apply (rule exI[of _ "map_terms_pre id (inv f) (rrename_terms (inv f)) id"])
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
   apply assumption
  apply (rule conjI)
   apply (rule trans)
    apply (rule terms_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 terms.rrename_comp0s terms.rrename_id0s
  apply (rule terms_pre.map_id0)
  apply (rule trans)
   apply (rule terms_pre.map_comp0[symmetric])
        apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp2 terms.rrename_comp0s terms.rrename_id0s
  apply (rule terms_pre.map_id0)
  done

lemma map_terms_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> inv (map_terms_pre (id::_::var_terms_pre \<Rightarrow> _) f (rrename_terms f) id) = map_terms_pre id (inv f) (rrename_terms (inv f)) id"
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
  apply assumption
  apply (rule inv_unique_comp)
   apply (rule trans)
    apply (rule terms_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
   defer
  apply (rule trans)
    apply (rule terms_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 inv_o_simp2 terms.rrename_comp0s terms.rrename_id0s terms_pre.map_id0
   apply (rule refl)+
  done

lemma Var_set1: "terms_ctor v = Var a \<Longrightarrow> a \<in> set1_terms_pre v"
  unfolding Var_def terms.TT_injects0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
    apply (drule iffD2[OF bij_imp_inv', rotated, of "map_terms_pre id f (rrename_terms f) id"])
     apply (rule bij_map_terms_pre)
      apply assumption+
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    unfolding map_terms_pre_inv_simp
    unfolding map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case
      id_def set1_terms_pre_def sum_set_simps ccpo_Sup_singleton
    apply (rule UnI1)
    apply (rule singletonI)
    done
  done

lemma Abs_set3: "terms_ctor v = Abs x \<tau> e \<Longrightarrow> \<exists>x' e'. terms_ctor v = Abs x' \<tau> e' \<and> x' \<in> set2_terms_pre v \<and> e' \<in> set3_terms_pre v"
  unfolding Abs_def terms.TT_injects0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
apply (drule iffD2[OF bij_imp_inv', rotated, of "map_terms_pre id f (rrename_terms f) id"])
     apply (rule bij_map_terms_pre)
      apply assumption+
    apply (rule exI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule exI[of _ "id"])
     apply (rule conjI bij_id supp_id_bound id_on_id)+
    apply (drule sym)
    unfolding terms.rrename_id0s terms_pre.map_id map_terms_pre_inv_simp
    unfolding map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case
      map_prod_def prod.case id_def
    apply assumption
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
unfolding set2_terms_pre_def set3_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] sum_set_simps
    map_sum_def sum.case Union_empty Un_empty_left map_prod_def prod.case prod_set_simps
      ccpo_Sup_singleton Un_empty_right id_on_def image_single[symmetric]
  unfolding terms.FFVars_rrenames[OF bij_imp_bij_inv supp_inv_bound]
  unfolding image_single image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv], symmetric]
    image_in_bij_eq[OF bij_imp_bij_inv] inv_inv_eq image_in_bij_eq[OF terms.rrename_bijs[OF bij_imp_bij_inv supp_inv_bound]]
  terms.rrename_inv_simps[OF bij_imp_bij_inv supp_inv_bound] inv_simp2
  unfolding terms.rrename_comps[OF bij_imp_bij_inv supp_inv_bound] inv_o_simp2 terms.rrename_ids
  apply (rule conjI bij_imp_bij_inv supp_inv_bound singletonI | assumption)+
  done
  done

lemma App_set4: "terms_ctor v = App e1 e2 \<Longrightarrow> e1 \<in> set4_terms_pre v \<and> e2 \<in> set4_terms_pre v"
  unfolding App_def terms.TT_injects0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
    apply (drule iffD2[OF bij_imp_inv', rotated, of "map_terms_pre id f (rrename_terms f) id"])
     apply (rule bij_map_terms_pre)
      apply assumption+
    unfolding map_terms_pre_inv_simp
    unfolding map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case
      map_prod_def prod.case
    unfolding id_def
    apply (drule sym)
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    unfolding set4_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] sum_set_simps
    map_sum_def sum.case Union_empty Un_empty_left map_prod_def prod.case prod_set_simps
      ccpo_Sup_singleton Un_empty_right
    apply (rule conjI)
     apply (rule UnI1)
     apply (rule singletonI)
    apply (rule UnI2)
    apply (rule singletonI)
    done
  done

lemma Abs_avoid: "|A::'a::var_terms_pre set| <o |UNIV::'a set| \<Longrightarrow> \<exists>x' e'. Abs x \<tau> e = Abs x' \<tau> e' \<and> x' \<notin> A"
  apply (drule terms.TT_fresh_nchotomys[of _ "Abs x \<tau> e"])
  apply (erule exE)
  apply (erule conjE)
   apply (drule sym)
  apply (frule Abs_set3)
  apply (erule exE conjE)+
  apply (rule exI)+
  apply (rule conjI)
   apply (rule trans)
    apply (rule sym)
    apply assumption
  apply (rotate_tac 2)
   apply assumption
  apply (drule iffD1[OF disjoint_iff])
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma TT_fresh_induct[case_names Bound Var App Abs]:
  assumes bound: "|A::'a set| <o |UNIV::'a::var_terms_pre set|"
  and Var: "\<And>a. P (Var a)"
  and App: "\<And>e1 e2. P e1 \<Longrightarrow> P e2 \<Longrightarrow> P (App e1 e2)"
  and Abs: "\<And>x \<tau> e. x \<notin> A \<Longrightarrow> P e \<Longrightarrow> P (Abs x \<tau> e)"
shows "P x"
  apply (rule terms.TT_fresh_co_induct)
   apply (rule bound)
  subgoal for v
    apply (rule Abs_terms_pre_cases[of v])
    subgoal for y
    apply (rule sum.exhaust[of y])
     apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    unfolding Var_def[symmetric]
     apply (rule Var)
    subgoal for y2
      apply (rule sum.exhaust[of y2])
       apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
      subgoal for y3
        apply (rule prod.exhaust[of y3])
        apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
        apply (frule arg_cong[of _ _ "Abs_terms_pre"])
        apply (rotate_tac -1)
        apply (drule arg_cong[of _ _ terms_ctor])
        unfolding App_def[symmetric]
        apply (drule App_set4)
        apply (erule conjE)
        apply (rule App)
         apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
         apply assumption
        apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
        apply assumption
        done
      subgoal for y3
        apply (rule prod.exhaust[of y3])
        subgoal for x b
          apply (rule prod.exhaust[of b])
          apply (frule arg_cong[of _ _ terms_ctor])
          apply (rotate_tac -1)
          apply (drule sym[THEN trans[rotated]])
           defer
           apply (rotate_tac -1)
           apply (drule sym)
           apply (drule Abs_set3)
           apply (erule exE conjE)+
           apply (rule iffD2[OF arg_cong[of _ _ P]])
          apply assumption
           apply (rule Abs)
            apply assumption
           apply assumption
          apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
          unfolding Abs_def[symmetric]
          apply (rule refl)
          done
        done
      done
    done
  done
  done

lemmas TT_plain_induct = TT_fresh_induct[OF emp_bound, case_names Var App Abs]

(* Term for variable substitution *)
(* TODO: Define with ML *)
abbreviation \<eta> :: "'a::var_terms_pre \<Rightarrow> ('a, 'b::var_terms_pre, 'c, 'd) terms_pre" where
  "\<eta> a \<equiv> Abs_terms_pre (Inl a)"

(* helpers *)
lemma notin_rangeE: "b \<notin> range f \<Longrightarrow> (\<And>x. b \<noteq> f x \<Longrightarrow> P) \<Longrightarrow> P"
  by fast
lemma nexists_setl: "\<nexists>x. y = Inl x \<Longrightarrow> Basic_BNFs.setl y = {}"
  by (metis sumE sum_set_simps(2))
lemma supp_swap_bound: "|supp (id (x := y, y := x :: 'a))| <o |UNIV::'a::var_terms_pre set|"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF supp_swap_le] finite_ordLess_infinite2])
    (auto simp: cinfinite_imp_infinite[OF terms.UNIV_cinfinite])
lemma ordLess_not_equal: "|A| <o |B| \<Longrightarrow> A \<noteq> B"
  using ordLess_irreflexive by blast
lemma bij_id_imsupp: "bij f \<Longrightarrow> f a = a \<Longrightarrow> a \<notin> imsupp f"
  unfolding imsupp_def supp_def
  by (simp add: bij_inv_eq_iff image_in_bij_eq)
lemma bij_not_eq_twice: "bij g \<Longrightarrow> g a \<noteq> a \<Longrightarrow> g (g a) \<noteq> g a"
  by simp
lemma bij_not_equal_iff: "bij f \<Longrightarrow> a \<noteq> b \<longleftrightarrow> f a \<noteq> f b"
  by simp
lemma fst_o_f: "fst \<circ> (\<lambda>(x, y). (f x, g x y)) = f \<circ> fst"
  by auto
lemma id_o_commute: "id \<circ> f = f \<circ> id" by simp
lemma case_lam_iff: "(\<lambda>x. f (case x of (a, b) \<Rightarrow> P a b)) = (\<lambda>(x, y). f (P x y))"
  by auto
lemma case_lam_app_iff: "(\<lambda>x. (case x of (a, b) \<Rightarrow> \<lambda>p. P a b p) t) = (\<lambda>(x, y). P x y t)"
  by auto
lemma exists_fresh: "|A::'a set| <o |UNIV::'a set| \<Longrightarrow> \<exists>a::'a. a \<notin> A"
  by (metis UNIV_eq_I ordLess_irreflexive)
lemma swap_fresh: "y \<notin> A \<Longrightarrow> x \<in> id(x := y, y := x) ` A \<Longrightarrow> False"
  by auto

(* eta axioms *)
lemma \<eta>_free: "set1_terms_pre (\<eta> a) = {a}"
  unfolding set1_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I]
  by auto
lemma \<eta>_inj: "\<eta> a = \<eta> b \<Longrightarrow> a = b"
  unfolding Abs_terms_pre_inject[OF UNIV_I UNIV_I] sum.inject
  by assumption
lemma \<eta>_compl_free: "x \<notin> range \<eta> \<Longrightarrow> set1_terms_pre x = {}"
  unfolding set1_terms_pre_def comp_def Un_empty sum.set_map UN_singleton UN_empty2
  apply (rule conjI)
   apply (rule Abs_terms_pre_cases[of x])
   apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding Abs_terms_pre_inverse[OF UNIV_I] Abs_terms_pre_inject[OF UNIV_I UNIV_I] image_iff bex_UNIV
   apply ((rule nexists_setl, assumption) | rule refl)+
  done
lemma \<eta>_natural: "|supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij g \<Longrightarrow> |supp (g::'b::var_terms_pre \<Rightarrow> 'b)| <o |UNIV::'b set|
  \<Longrightarrow> map_terms_pre f g h i \<circ> \<eta> = \<eta> \<circ> f"
  unfolding comp_def map_terms_pre_def Abs_terms_pre_inverse[OF UNIV_I] map_sum.simps
  apply (rule refl)
  done

(* tsubst theorems *)
definition "VVr a \<equiv> terms_ctor (\<eta> a)"

lemma VVr_inj: "VVr a = VVr b \<Longrightarrow> a = b"
  unfolding VVr_def
  apply (rule \<eta>_inj)
  apply (drule iffD1[OF terms.TT_injects0])
  apply (erule exE)
  apply (erule conjE)+
  unfolding fun_cong[OF \<eta>_natural[OF supp_id_bound, unfolded comp_def]]
  unfolding id_def
  apply assumption
  done

lemma rrename_VVr:
  assumes "bij (f::'a::var_terms_pre \<Rightarrow> 'a)" "|supp f| <o |UNIV::'a set|"
  shows "rrename_terms f (VVr a) = VVr (f a)"
  unfolding VVr_def terms.rrename_cctors[OF assms]
  apply (rule arg_cong[of _ _ terms_ctor])
  apply (rule trans)
   apply (rule fun_cong[OF \<eta>_natural[unfolded comp_def]])
     apply (rule assms)+
  apply (rule refl)
  done

definition SSupp :: "('a::var_terms_pre \<Rightarrow> 'a terms) \<Rightarrow> 'a set" where
  "SSupp f \<equiv> { a. f a \<noteq> VVr a }"

definition IImsupp :: "('a::var_terms_pre \<Rightarrow> 'a terms) \<Rightarrow> 'a set" where
  "IImsupp f \<equiv> SSupp f \<union> (\<Union> a \<in> SSupp f. FFVars_terms (f a))"

lemma in_IImsupp: "f a \<noteq> VVr a \<Longrightarrow> z \<in> FFVars_terms (f a) \<Longrightarrow> z \<in> IImsupp f"
  unfolding IImsupp_def SSupp_def
  apply (rule UnI2)
  apply (rule iffD2[OF UN_iff])
  apply (rule bexI)
   apply assumption
  apply (rule CollectI)
  apply assumption
  done

lemma IImsupp_VVr: "g a \<noteq> a \<Longrightarrow> IImsupp f \<inter> imsupp g = {} \<Longrightarrow> f a = VVr a"
  unfolding imsupp_def supp_def IImsupp_def SSupp_def
  apply (drule trans[OF Int_commute])
  apply (drule iffD1[OF disjoint_iff])
  apply (erule allE)
  apply (erule impE)
   apply (rule UnI1)
   apply (rule CollectI)
   apply assumption
  unfolding Un_iff de_Morgan_disj mem_Collect_eq not_not
  apply (erule conjE)
  apply assumption
  done

lemma IImsupp_imsupp_rrename_commute:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a terms" and g::"'a \<Rightarrow> 'a"
  assumes "IImsupp f \<inter> imsupp g = {}" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "rrename_terms g \<circ> f = f \<circ> g"
  apply (rule ext)
  unfolding comp_def
  subgoal for a
  apply (rule case_split[of "g a = a"])
   apply (rule case_split[of "f a = VVr a"])
    apply (rule trans)
     apply (rule arg_cong[of _ _ "rrename_terms g"])
     apply assumption
    apply (rule trans)
     apply (rule rrename_VVr)
      apply (rule assms)+
    apply (rule trans)
     apply (rule arg_cong[of _ _ VVr])
     apply assumption
    apply (rule sym)
    apply (rule trans)
     apply (rule arg_cong[of _ _ f])
     apply assumption
    apply assumption
   apply (rule trans)
    apply (rule terms.rrename_cong_ids)
        apply (rule assms)+
      apply (drule in_IImsupp)
       apply assumption
      apply (drule mp[OF spec[OF iffD1[OF disjoint_iff assms(1)]]])
      apply (rule not_in_imsupp_same)
    apply assumption
   apply (rule sym)
   apply (rule trans)
    apply (rule arg_cong[of _ _ f])
    apply assumption
   apply (rule refl)
  apply (rule trans)
   apply (rule arg_cong[of _ _ "rrename_terms g"])
   defer
   apply (rule trans)
    apply (rule rrename_VVr)
       apply (rule assms)+
     defer
     apply (rule IImsupp_VVr)
      apply assumption
     apply (rule assms)
    apply (rule sym)
    apply (rule IImsupp_VVr)
     apply (drule bij_not_eq_twice[rotated])
      apply (rule assms)
     apply assumption
    apply (rule assms)
    done
  done

lemma SSupp_VVr_empty: "SSupp VVr = {}"
  unfolding SSupp_def
  apply (rule iffD2[OF set_eq_iff])
  apply (rule allI)
  apply (rule iffI)
   apply (drule iffD1[OF mem_Collect_eq])
  unfolding atomize_not not_not empty_iff
   apply (rule refl)
  apply (erule FalseE)
  done

lemma IImsupp_VVr_empty: "IImsupp VVr = {}"
  unfolding IImsupp_def SSupp_VVr_empty UN_empty Un_empty_left
  apply (rule refl)
  done

lemma SSupp_VVr_bound: "|SSupp VVr| <o |UNIV::'a set|"
  unfolding SSupp_VVr_empty
  apply (rule emp_bound)
  done

lemma SSupp_comp_subset:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a terms" and g::"'a \<Rightarrow> 'a"
  assumes "|supp g| <o |UNIV::'a set|" "bij g"
  shows "SSupp (f \<circ> g) \<subseteq> SSupp f \<union> supp g"
  unfolding SSupp_def supp_def
  by auto

lemma SSupp_comp_bound:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a terms" and g::"'a \<Rightarrow> 'a"
  assumes "|SSupp f| <o |UNIV::'a set|" "|supp g| <o |UNIV::'a set|" "bij g"
  shows "|SSupp (f \<circ> g)| <o |UNIV::'a set|"
  apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_comp_subset]])
    apply (rule assms terms.Un_bound)+
  done

lemma SSupp_comp_rename_subset:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a terms" and g::"'a \<Rightarrow> 'a"
  assumes "|supp g| <o |UNIV::'a set|" "bij g"
  shows "SSupp (rrename_terms g \<circ> f) \<subseteq> SSupp f \<union> supp g"
  unfolding SSupp_def supp_def
  by (auto simp: rrename_VVr assms)

lemma SSupp_comp_rename_bound:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a terms" and g::"'a \<Rightarrow> 'a"
  assumes "|SSupp f| <o |UNIV::'a set|" "|supp g| <o |UNIV::'a set|" "bij g"
  shows "|SSupp (rrename_terms g \<circ> f)| <o |UNIV::'a set|"
  apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_comp_rename_subset]])
    apply (rule assms terms.Un_bound)+
  done

typedef 'a::var_terms_pre SSfun = "{ f::'a \<Rightarrow> 'a terms. |SSupp f| <o |UNIV::'a set| }"
  by (auto intro!: exI[of _ VVr] simp: SSupp_VVr_bound)

lemma IImsupp_comp_image:
  assumes "bij f" "|supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set|"
  shows "IImsupp (rrename_terms f \<circ> Rep_SSfun p \<circ> inv f) = f ` IImsupp (Rep_SSfun p)"
  unfolding IImsupp_def SSupp_def image_Un image_UN
   terms.FFVars_rrenames[OF assms, symmetric] comp_def bij_image_Collect_eq[OF assms(1)]
  apply (rule iffD2[OF set_eq_iff])
  apply (rule allI)
  apply (rule iffI)
   apply (erule UnE)
    apply (drule iffD1[OF mem_Collect_eq])
    apply (rule UnI1)
    apply (rule iffD2[OF mem_Collect_eq])
    apply (drule iffD1[OF bij_not_equal_iff, rotated])
     apply (rule terms.rrename_bijs)
  apply (rule bij_imp_bij_inv)
      apply (rule assms supp_inv_bound)+
  unfolding terms.rrename_comps[OF assms bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]]
    inv_o_simp1[OF assms(1)] terms.rrename_ids rrename_VVr[OF bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]]
    apply assumption
   apply (rule UnI2)
  unfolding UN_iff
   apply (erule bexE)
   apply (drule iffD1[OF mem_Collect_eq])
   apply (rule bexI)
    apply assumption
   apply (rule iffD2[OF mem_Collect_eq])
   apply (rule iffD2[OF bij_not_equal_iff])
    apply (rule terms.rrename_bijs)
     apply (rule assms)+
  unfolding rrename_VVr[OF assms] inv_simp2[OF assms(1)]
   apply assumption
  apply (erule UnE)
   apply (rule UnI1)
   apply (drule iffD1[OF mem_Collect_eq])
   apply (rule iffD2[OF mem_Collect_eq])
   apply (rule iffD2[OF bij_not_equal_iff])
    apply (rule terms.rrename_bijs)
     apply (rule bij_imp_bij_inv)
     apply (rule assms supp_inv_bound)+
  unfolding terms.rrename_comps[OF assms bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]]
    inv_o_simp1[OF assms(1)] terms.rrename_ids rrename_VVr[OF bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]]
  apply assumption
  apply (rule UnI2)
  unfolding UN_iff
  apply (erule bexE)
  apply (rule bexI[of _ "f _"])
  unfolding bij_not_equal_iff[OF terms.rrename_bijs[OF assms], of _ "VVr _"]
    inv_simp1[OF assms(1)]
   apply assumption
  apply (rule CollectI)
  unfolding inv_simp1[OF assms(1)]
  apply (rule iffD1[OF bij_not_equal_iff[OF terms.rrename_bijs[OF assms]]])
  apply (drule iffD1[OF mem_Collect_eq])
  unfolding rrename_VVr[OF assms]
  apply assumption
  done

definition compSS :: "('a::var_terms_pre \<Rightarrow> 'a) \<Rightarrow> 'a SSfun \<Rightarrow> 'a SSfun" where
  "compSS f p \<equiv> Abs_SSfun (rrename_terms f \<circ> Rep_SSfun p \<circ> inv f)"

definition PFVars :: "'a::var_terms_pre SSfun \<Rightarrow> 'a set" where
  "PFVars p \<equiv> IImsupp (Rep_SSfun p)"

(* Parameter axioms *)
lemma compSS_id0: "compSS id = id"
  unfolding compSS_def terms.rrename_id0s inv_id id_o o_id Rep_SSfun_inverse
  unfolding id_def
  by (rule refl)

lemma compSS_comp0:
  fixes f g::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|" "bij f" "|supp g| <o |UNIV::'a set|" "bij g"
  shows "compSS (f \<circ> g) = compSS f \<circ> compSS g"
  unfolding compSS_def terms.rrename_comp0s[OF assms(4,3,2,1), symmetric] o_inv_distrib[OF assms(2,4)] comp_assoc[symmetric]
  apply (rule ext)
  apply (rule sym)
  apply (rule trans[OF comp_apply])
  apply (rule arg_cong[of _ _ Abs_SSfun])
  apply (rule trans)
  apply (rule trans[OF comp_assoc])
   apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
   apply (rule arg_cong2[OF _ refl, of _ _ "(\<circ>)"])
   apply (rule Abs_SSfun_inverse)
   apply (rule iffD2[OF mem_Collect_eq])
   apply (rule SSupp_comp_bound)
     apply (rule SSupp_comp_rename_bound)
       apply (rule iffD1[OF mem_Collect_eq Rep_SSfun])
      apply (rule assms supp_inv_bound bij_imp_bij_inv)+
  unfolding comp_assoc[symmetric]
  apply (rule refl)
  done

lemma compSS_cong_id:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
shows "(\<And>a. a \<in> PFVars p \<Longrightarrow> f a = a) \<Longrightarrow> compSS f p = p"
  unfolding compSS_def PFVars_def
  apply (rule trans)
   apply (rule arg_cong[of _ _ Abs_SSfun])
   apply (rule arg_cong2[OF _ refl, of _ _ "(\<circ>)"])
   apply (rule IImsupp_imsupp_rrename_commute)
     apply (rule iffD2[OF disjoint_iff])
     apply (rule allI)
     apply (rule impI)
     apply (rule bij_id_imsupp)
      apply (rule assms)
  apply assumption
    apply (rule assms)+
  unfolding comp_assoc inv_o_simp2[OF assms(1)] o_id Rep_SSfun_inverse
  apply (rule refl)
  done

lemma PFVars_compSS: "|supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij f \<Longrightarrow>
  PFVars (compSS f p) = f ` PFVars p"
  unfolding compSS_def PFVars_def
  apply (rule trans)
   apply (rule arg_cong[of _ _ IImsupp])
   apply (rule Abs_SSfun_inverse)
   apply (rule iffD2[OF mem_Collect_eq])
   apply (rule SSupp_comp_bound)
     apply (rule SSupp_comp_rename_bound)
       apply (rule iffD1[OF mem_Collect_eq Rep_SSfun])
      apply (assumption | rule supp_inv_bound bij_imp_bij_inv)+
  apply (rule IImsupp_comp_image)
   apply assumption+
  done

lemma small_PFVars: "|PFVars (p::'a::var_terms_pre SSfun)| <o |UNIV::'a set|"
  unfolding PFVars_def IImsupp_def
  apply (rule terms_pre.Un_bound)
   apply (rule iffD1[OF mem_Collect_eq Rep_SSfun])
  apply (rule terms_pre.UNION_bound)
   apply (rule iffD1[OF mem_Collect_eq Rep_SSfun])
  apply (rule terms.card_of_FFVars_bounds)
  done

definition isVVr :: "'a::var_terms_pre terms \<Rightarrow> bool" where
  "isVVr t \<equiv> (\<exists>a. t = VVr a)"

definition asVVr :: "'a::var_terms_pre terms \<Rightarrow> 'a" where
  "asVVr t \<equiv> if isVVr t then (SOME a. VVr a = t) else undefined"

definition CCTOR :: "('a::var_terms_pre, 'a, 'a terms \<times> ('a SSfun \<Rightarrow> 'a terms), 'a terms \<times> ('a SSfun \<Rightarrow> 'a terms)) terms_pre \<Rightarrow> 'a SSfun \<Rightarrow> 'a terms" where
  "CCTOR = (\<lambda>F p. if isVVr (terms_ctor (map_terms_pre id id fst fst F)) then
       Rep_SSfun p (asVVr (terms_ctor (map_terms_pre id id fst fst F)))
     else
       terms_ctor (map_terms_pre id id ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) F))"

definition PUmap where "PUmap f t pu \<equiv> \<lambda>p. rrename_terms f (pu (compSS (inv f) p))"

lemma isVVr_rename:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "isVVr (rrename_terms f x) \<longleftrightarrow> isVVr x"
  unfolding isVVr_def
  apply (rule iffI)
   apply (erule exE)
   apply (rule exI[of _ "inv f _"])
  unfolding rrename_VVr[OF bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms], symmetric]
   terms.rrename_inv_simps[OF assms, symmetric]
   apply (rule iffD2[OF bij_inv_rev])
    apply (rule terms.rrename_bijs[OF assms])
   apply (rule sym)
   apply assumption
  apply (erule exE)
  apply (rule exI[of _ "f _"])
  unfolding rrename_VVr[OF assms, symmetric]
  apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule refl)
  done

lemma asVVr_rename:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "isVVr x"
  shows "asVVr (rrename_terms f x) = f (asVVr x)"
  unfolding asVVr_def isVVr_rename[OF assms(1,2)] if_P[OF assms(3)]
    VVr_def bij_inv_rev[OF terms.rrename_bijs[OF assms(1,2)], symmetric]
    terms.rrename_inv_simps[OF assms(1,2)] terms.rrename_cctors[OF bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms(1,2)]]
    fun_cong[OF \<eta>_natural[OF supp_inv_bound[OF assms(1,2)] bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms(1,2)], unfolded comp_def]]
  apply (rule some_equality)
  unfolding inv_simp1[OF assms(1)]
   apply (rule sym)
   apply (rule exE[OF assms(3)[unfolded isVVr_def VVr_def]])
   apply (rule someI)
   apply (rule sym)
   apply assumption
  apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding VVr_def[symmetric]
  apply (rule iffD1[OF bij_inv_rev[OF assms(1)]])
  apply (rule VVr_inj)
  apply (rule someI)
  apply (rule refl)
  done

lemma asVVr_VVr: "asVVr (VVr a) = a"
  unfolding asVVr_def isVVr_def
  apply (rule trans)
   apply (rule if_P)
   apply (rule exI)
   apply (rule refl)
  apply (rule some_equality)
   apply (rule refl)
  apply (rule VVr_inj)
  apply assumption
  done

(* CCTOR axioms *)
lemma Umap_Uctor:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "rrename_terms f (CCTOR x p) =
  CCTOR (map_terms_pre f f (\<lambda>(t, pu). (rrename_terms f t, PUmap f t pu)) (\<lambda>(t, pu). (rrename_terms f t, PUmap f t pu)) x) (compSS f p)"
  unfolding CCTOR_def
  apply (rule case_split[of "isVVr (terms_ctor (map_terms_pre id id fst fst x))"])
  unfolding if_P terms_pre.map_comp[OF assms(2,1,2) supp_id_bound bij_id supp_id_bound]
    fst_o_f id_o_commute
  unfolding terms_pre.map_comp[OF supp_id_bound bij_id supp_id_bound assms(2,1,2), symmetric]
    terms.rrename_cctors[OF assms, symmetric] isVVr_rename[OF assms] if_P asVVr_rename[OF assms]
  apply (raw_tactic \<open>SELECT_GOAL (Ctr_Sugar_Tactics.unfold_thms_tac @{context} @{thms compSS_def}) 1\<close>)
    apply (rule sym)
    apply (rule trans)
     apply (rule fun_cong[OF Abs_SSfun_inverse])
     apply (rule iffD2[OF mem_Collect_eq])
     apply (rule SSupp_comp_bound)
       apply (rule SSupp_comp_rename_bound)
         apply (rule iffD1[OF mem_Collect_eq Rep_SSfun])
        apply (rule assms supp_inv_bound bij_imp_bij_inv)+
  apply (raw_tactic \<open>SELECT_GOAL (Ctr_Sugar_Tactics.unfold_thms_tac @{context} @{thms comp_def inv_simp1[OF assms(1)] }) 1\<close>)
    apply (rule refl)

  (* case 2 *)
    unfolding if_not_P
    apply (rule trans)
     apply (rule terms.rrename_cctors)
      apply (rule assms)+
    unfolding terms_pre.map_comp[OF supp_id_bound bij_id supp_id_bound assms(2,1,2)]
      o_id comp_assoc comp_def[of snd] case_lam_iff snd_conv PUmap_def
    unfolding comp_def case_lam_iff case_lam_app_iff
      fun_cong[OF compSS_comp0[unfolded comp_def], symmetric, OF supp_inv_bound[OF assms] bij_imp_bij_inv[OF assms(1)] assms(2,1)]
      inv_simp1[OF assms(1)] id_def[symmetric] compSS_id0
    unfolding id_def case_prod_beta
    apply (rule refl)
    done

lemma UFVars_Uctor:
  assumes "(\<And>t pu p. (t, pu) \<in> set3_terms_pre x \<union> set4_terms_pre x \<Longrightarrow> FFVars_terms (pu p) \<subseteq> FFVars_terms t \<union> PFVars p)"
  "set2_terms_pre x \<inter> PFVars p = {}"
 shows "FFVars_terms (CCTOR x p) \<subseteq> FFVars_terms (terms_ctor (map_terms_pre id id fst fst x)) \<union> PFVars p"
  unfolding CCTOR_def
  apply (rule case_split[of "isVVr (terms_ctor (map_terms_pre id id fst fst x))"])
  unfolding if_P if_not_P
  subgoal
    unfolding isVVr_def
    apply (erule exE)
    subgoal premises prems for a
      apply (rule case_split[of "Rep_SSfun p a = VVr a"])
      unfolding prems asVVr_VVr PFVars_def IImsupp_def SSupp_def
      subgoal premises prems2
        unfolding prems2
        apply (rule Un_upper1)
        done
      apply (rule subset_trans[OF _ Un_upper2])+
      apply (rule iffD2[OF subset_iff])
      apply (rule allI)
      apply (rule impI)
      apply (rule iffD2[OF UN_iff])
      apply (rule bexI)
       apply assumption
      apply (rule iffD2[OF mem_Collect_eq])
      apply assumption
      done
    done
  unfolding terms.FFVars_cctors terms_pre.set_map[OF supp_id_bound bij_id supp_id_bound] image_id
    image_comp comp_def[of FFVars_terms] PFVars_def
  apply (rule Un_mono')+
    apply (rule Un_upper1)
   apply (rule iffD2[OF arg_cong2[OF refl _, of _ _ "(\<subseteq>)"]])
    apply (rule Diff_Un_disjunct)
  unfolding PFVars_def[symmetric]
  apply (rule assms(2))
   apply (rule Diff_mono[OF _ subset_refl])
   apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
    apply (rule UN_extend_simps(2))
   apply (rule subset_If)
  unfolding UN_empty'
    apply (rule empty_subsetI)
   apply (rule UN_mono[OF subset_refl])
  unfolding comp_def[of _ snd]
  apply (rule assms(1))
    unfolding surjective_pairing[symmetric]
     apply (rule UnI1)
    apply assumption
  apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
   apply (rule UN_extend_simps(2))
  apply (rule subset_If)
  unfolding UN_empty'
   apply (rule empty_subsetI)
  apply (rule UN_mono[OF subset_refl])
  apply (rule assms(1))
    unfolding surjective_pairing[symmetric]
    apply (rule UnI2)
    apply assumption
    done

local_setup \<open>fn lthy =>
let
  val res = hd (the (Symtab.lookup (Data.get (Context.Proof lthy)) name))
  fun rtac ctxt = resolve_tac ctxt o single

  val model_axioms = {
   small_avoiding_sets = [fn ctxt => rtac ctxt @{thm emp_bound} 1],
   Umap_id0 = fn ctxt => rtac ctxt @{thm terms.rrename_id0s} 1,
   Umap_comp0 = fn ctxt => rtac ctxt @{thm terms.rrename_comp0s[symmetric]} 1 THEN ALLGOALS (assume_tac ctxt),
    Umap_cong_ids = [fn ctxt => rtac ctxt @{thm terms.rrename_cong_ids} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1)],
    UFVars_Umap = [fn ctxt => rtac ctxt @{thm terms.FFVars_rrenames} 1 THEN ALLGOALS (assume_tac ctxt)],
    Umap_Uctor = fn ctxt => rtac ctxt @{thm Umap_Uctor[unfolded PUmap_def]} 1 THEN ALLGOALS (assume_tac ctxt),
    UFVars_subsets = [fn ctxt => Ctr_Sugar_Tactics.unfold_thms_tac ctxt @{thms Un_empty_right} THEN rtac ctxt @{thm UFVars_Uctor} 1 THEN Goal.assume_rule_tac ctxt 1 THEN assume_tac ctxt 1]
  };

  val parameter_axioms = {
    Pmap_id0 = fn ctxt => rtac ctxt @{thm compSS_id0} 1,
    Pmap_comp0 = fn ctxt => rtac ctxt @{thm compSS_comp0} 1 THEN ALLGOALS (assume_tac ctxt),
    Pmap_cong_ids = [fn ctxt => rtac ctxt @{thm compSS_cong_id} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1)],
    PFVars_Pmaps = [fn ctxt => rtac ctxt @{thm PFVars_compSS} 1 THEN ALLGOALS (assume_tac ctxt)],
    small_PFVarss = [fn ctxt => rtac ctxt @{thm small_PFVars} 1]
  };

  val model = {
    fp_result = res,
    U = @{typ "'a::var_terms_pre terms"},
    UFVars = [@{term "\<lambda>(_::'a terms). FFVars_terms :: _ \<Rightarrow> 'a::var_terms_pre set"}],
    Umap = @{term "\<lambda>(f::'a::var_terms_pre \<Rightarrow> 'a) (_::'a terms). rrename_terms f"},
    Uctor = @{term "CCTOR :: _ \<Rightarrow> _ \<Rightarrow> 'a::var_terms_pre terms"},
    avoiding_sets = [@{term "{} :: 'a::var_terms_pre set"}],
    parameters = {
      P = @{typ "'a::var_terms_pre SSfun"},
      PFVarss = [@{term "PFVars :: _ \<Rightarrow> 'a::var_terms_pre set"}],
      Pmap = @{term "compSS :: _ \<Rightarrow> _ \<Rightarrow> 'a::var_terms_pre SSfun"},
      axioms = parameter_axioms
    },
    axioms = model_axioms
  } : (Proof.context -> tactic) MRBNF_Recursor.model;
  
  val (rec_res, lthy) = MRBNF_Recursor.create_binding_recursor (Binding.prefix_name "tv") model @{binding tvsubst} lthy
  val _ = @{print} rec_res
  val notes =
    [("tvsubst_swap", [#rec_swap rec_res]),
     ("tvsubst_UFVars", #rec_UFVarss rec_res),
     ("tvsubst_Uctor", [#rec_Uctor rec_res])
    ] |> (map (fn (thmN, thms) =>
      (((Binding.name thmN), []), [(thms, [])])
    ));
  val (noted, lthy) = Local_Theory.notes notes lthy
in lthy end
\<close>
print_theorems

definition tvsubst :: "('a::var_terms_pre \<Rightarrow> 'a terms) \<Rightarrow> 'a terms \<Rightarrow> 'a terms" where
  "tvsubst f x \<equiv> tvff0_tvsubst x (Abs_SSfun f)"

lemma isVVr_VVr: "isVVr (VVr x)"
  unfolding isVVr_def
  apply (rule exI)
  apply (rule refl)
  done

lemma \<eta>_set2: "set2_terms_pre (\<eta> (a::'a::var_terms_pre) :: ('a, 'b::var_terms_pre, 'c, 'd) terms_pre) = {}"
  apply (rule iffD2[OF set_eq_iff])
  apply (rule allI)
  unfolding empty_iff
  apply (rule iffI)
  apply (rule exE[OF exists_fresh])
  apply (rule terms_pre.set_bd_UNIV(2)[of "\<eta> a :: ('a, 'b::var_terms_pre, 'c, 'd) terms_pre"])
  subgoal for x y
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
   apply (rule arg_cong[of _ _ set2_terms_pre])
   apply (rule fun_cong[OF \<eta>_natural[OF supp_id_bound bij_swap supp_swap_bound, unfolded o_id, symmetric], unfolded comp_def, of _ x y])
    unfolding terms_pre.set_map[OF supp_id_bound bij_swap supp_swap_bound]
    apply (rule swap_fresh)
     apply assumption
    apply assumption
    done
   apply (rule FalseE)
   apply assumption
  done

lemma forall_in_eq_UNIV: "\<forall>c. (c::'a) \<in> X \<Longrightarrow> X = (UNIV :: 'a set)" by blast
lemma image_const: "a \<in> X \<Longrightarrow> \<forall>c. c \<in> (\<lambda>_. c) ` X" by simp
lemma ordIso_ordLess_False: "a =o b \<Longrightarrow> a <o b \<Longrightarrow> False"
  by (simp add: not_ordLess_ordIso)

lemma \<eta>_set3: "set3_terms_pre (\<eta> (a::'a::var_terms_pre) :: ('a, 'b::var_terms_pre, 'c, 'd) terms_pre) = {}"
  apply (rule iffD2[OF set_eq_iff])
  apply (rule allI)
  unfolding empty_iff
  apply (rule iffI)
   apply (drule image_const)
   apply (drule iffD1[OF all_cong1, rotated])
    apply (rule arg_cong2[OF refl, of _ _ "(\<in>)"])
     apply (rule terms_pre.set_map[OF supp_id_bound bij_id supp_id_bound, symmetric])
  unfolding fun_cong[OF \<eta>_natural[OF supp_id_bound bij_id supp_id_bound], unfolded o_id, unfolded comp_def]
   apply (drule forall_in_eq_UNIV)
   apply (drule trans[symmetric])
    apply (rule conjunct1[OF card_order_on_Card_order[OF terms_pre.bd_card_order]])
   apply (drule card_of_ordIso_subst)
   apply (drule ordIso_symmetric)
   apply (drule ordIso_transitive)
    apply (rule ordIso_symmetric)
    apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
    apply (rule conjunct2[OF card_order_on_Card_order[OF terms_pre.bd_card_order]])
   apply (rule ordIso_ordLess_False)
    apply assumption
   apply (rule terms_pre.set_bd)
  apply (rule FalseE)
  apply assumption
  done

(* Same tactic as for set3 *)
lemma \<eta>_set4: "set4_terms_pre (\<eta> (a::'a::var_terms_pre) :: ('a, 'b::var_terms_pre, 'c, 'd) terms_pre) = {}"
  apply (rule iffD2[OF set_eq_iff])
  apply (rule allI)
  unfolding empty_iff
  apply (rule iffI)
   apply (drule image_const)
   apply (drule iffD1[OF all_cong1, rotated])
    apply (rule arg_cong2[OF refl, of _ _ "(\<in>)"])
     apply (rule terms_pre.set_map[OF supp_id_bound bij_id supp_id_bound, symmetric])
  unfolding fun_cong[OF \<eta>_natural[OF supp_id_bound bij_id supp_id_bound], unfolded o_id, unfolded comp_def]
   apply (drule forall_in_eq_UNIV)
   apply (drule trans[symmetric])
    apply (rule conjunct1[OF card_order_on_Card_order[OF terms_pre.bd_card_order]])
   apply (drule card_of_ordIso_subst)
   apply (drule ordIso_symmetric)
   apply (drule ordIso_transitive)
    apply (rule ordIso_symmetric)
    apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
    apply (rule conjunct2[OF card_order_on_Card_order[OF terms_pre.bd_card_order]])
   apply (rule ordIso_ordLess_False)
    apply assumption
   apply (rule terms_pre.set_bd)
  apply (rule FalseE)
  apply assumption
  done

lemma FVars_VVr: "FFVars_terms (VVr a) = {a}"
  unfolding VVr_def terms.FFVars_cctors \<eta>_set2 \<eta>_set3 \<eta>_set4 UN_empty Diff_empty Un_empty_right
  apply (rule \<eta>_free)
  done

lemma tvsubst_VVr: "|SSupp (f::'a::var_terms_pre \<Rightarrow> 'a terms)| <o |UNIV::'a set| \<Longrightarrow> tvsubst f (VVr x) = f x"
  unfolding tvsubst_def VVr_def
  apply (rule trans)
   apply (rule tvsubst_Uctor)
    apply (rule trans[OF arg_cong2[OF \<eta>_set2 refl, of "(\<inter>)"]])
    apply (rule Int_empty_left)
  unfolding tvnoclash_terms_def
   apply (rule trans[OF arg_cong2[OF \<eta>_set2 refl, of "(\<inter>)"]])
   apply (rule Int_empty_left)
  unfolding CCTOR_def terms_pre.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound]
    id_o comp_def[of fst] fst_conv id_def[symmetric] terms_pre.map_id VVr_def[symmetric] if_P[OF isVVr_VVr] asVVr_VVr
  apply (rule fun_cong[OF Abs_SSfun_inverse])
  apply (rule iffD2[OF mem_Collect_eq])
  apply assumption
  done

lemma tvsubst_cctor_not_isVVr: "|SSupp (f::'a::var_terms_pre \<Rightarrow> 'a terms)| <o |UNIV::'a set| \<Longrightarrow> set2_terms_pre x \<inter> IImsupp f = {} \<Longrightarrow> tvnoclash_terms x \<Longrightarrow>
  \<not>isVVr (terms_ctor x) \<Longrightarrow> tvsubst f (terms_ctor x) = terms_ctor (map_terms_pre id id (tvsubst f) (tvsubst f) x)"
  unfolding tvsubst_def
  apply (rule trans)
   apply (rule tvsubst_Uctor)
  unfolding PFVars_def Un_empty_right
    apply (rule trans[OF arg_cong2[OF refl, of _ _ "(\<inter>)"]])
     apply (rule arg_cong[of _ _ IImsupp])
     apply (rule Abs_SSfun_inverse)
     apply (rule iffD2[OF mem_Collect_eq])
     apply assumption
    apply assumption
   apply assumption
  unfolding CCTOR_def terms_pre.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound]
    id_o comp_def[of fst] fst_conv id_def[symmetric] terms_pre.map_id if_not_P
  unfolding comp_def snd_conv
  apply (rule refl)
  done

lemma tvsubst_Var: "|SSupp (f::'a::var_terms_pre \<Rightarrow> 'a terms)| <o |UNIV::'a set| \<Longrightarrow> tvsubst f (Var x) = f x"
  unfolding Var_def VVr_def[symmetric]
  apply (rule tvsubst_VVr)
  apply assumption
  done

lemma VVr_eq_Var: "VVr a = Var a"
  unfolding VVr_def Var_def
  by (rule refl)

lemma terms_isVVr:
  "isVVr (Var a)"
  "\<not>isVVr (App e1 e2)"
  "\<not>isVVr (Abs x \<tau> e)"
  unfolding isVVr_def VVr_eq_Var
  by auto

lemma tvsubst_App: "|SSupp (f::'a::var_terms_pre \<Rightarrow> 'a terms)| <o |UNIV::'a set| \<Longrightarrow> tvsubst f (App e1 e2) = App (tvsubst f e1) (tvsubst f e2)"
  unfolding App_def
  apply (rule trans)
   apply (rule tvsubst_cctor_not_isVVr)
      apply assumption
  unfolding set2_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case sum_set_simps
    Union_empty Un_empty_left ccpo_Sup_singleton tvnoclash_terms_def
     apply (rule Int_empty_left)+
   apply (rule terms_isVVr[unfolded App_def])
  unfolding map_terms_pre_def comp_def map_sum_def Abs_terms_pre_inverse[OF UNIV_I] sum.case
    map_prod_def prod.case
  apply (rule refl)
  done
lemma tvsubst_Abs: "|SSupp (f::'a::var_terms_pre \<Rightarrow> 'a terms)| <o |UNIV::'a set| \<Longrightarrow> x \<notin> IImsupp f \<Longrightarrow> tvsubst f (Abs x \<tau> e) = Abs x \<tau> (tvsubst f e)"
  unfolding Abs_def
  apply (rule trans)
   apply (rule tvsubst_cctor_not_isVVr)
      apply assumption
  unfolding set2_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case
    map_prod_def prod.case sum_set_simps Union_empty prod_set_simps ccpo_Sup_singleton Un_empty_left
  Un_empty_right disjoint_iff tvnoclash_terms_def set1_terms_pre_def set4_terms_pre_def UN_empty empty_iff not_False_eq_True
     apply (rule allI)
     apply (rule impI)
     apply (drule singletonD)
     apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply assumption
    apply (rule allI)
    apply (rule impI)
    apply (rule TrueI)
   apply (rule terms_isVVr[unfolded Abs_def])
  unfolding map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case
    map_prod_def prod.case id_def
  apply (rule refl)
  done
lemmas tvsubst_simps = tvsubst_Var tvsubst_App tvsubst_Abs

lemma vvsubst_Var: "|supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> vvsubst f (Var a) = Var (f a)"
  unfolding Var_def
  apply (rule trans)
   apply (rule terms_cctor)
     apply assumption
  unfolding \<eta>_set2 noclash_terms_def fun_cong[OF \<eta>_natural[OF _ bij_id supp_id_bound], unfolded comp_def]
    apply (rule Int_empty_left)+
  apply (rule refl)
  done
lemma vvsubst_App: "|supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> vvsubst f (App e1 e2) = App (vvsubst f e1) (vvsubst f e2)"
  unfolding App_def
  apply (rule trans)
   apply (rule terms_cctor)
     apply assumption
  unfolding set2_terms_pre_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def comp_def sum.case sum_set_simps
    Union_empty Un_empty_left Un_empty_right cSup_singleton noclash_terms_def map_terms_pre_def map_prod_def prod.case
    apply (rule Int_empty_left)+
  apply (rule refl)
  done
lemma vvsubst_Abs: "|supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> x \<notin> imsupp f \<Longrightarrow> vvsubst f (Abs x \<tau> e) = Abs x \<tau> (vvsubst f e)"
  unfolding Abs_def
  apply (rule trans)
   apply (rule terms_cctor)
     apply assumption
  unfolding set2_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case sum_set_simps
    Union_empty Un_empty_left map_prod_def prod.case prod_set_simps cSup_singleton Un_empty_right
    noclash_terms_def set1_terms_pre_def set4_terms_pre_def UN_empty map_terms_pre_def id_def
    apply (rule iffD2[OF disjoint_iff])
    apply (rule allI)
    apply (rule impI)
    apply (drule singletonD)
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply assumption
   apply (rule Int_empty_right)
  apply (rule refl)
  done
lemmas vvsubst_simps = vvsubst_Var vvsubst_App vvsubst_Abs

lemma FFVars_tvsubst_weak:
  assumes "|SSupp (f::'a::var_terms_pre \<Rightarrow> 'a terms)| <o |UNIV::'a set|"
shows "FFVars_terms (tvsubst f t) \<subseteq> FFVars_terms t \<union> IImsupp f"
  unfolding tvsubst_def
  apply (rule tvsubst_UFVars[unfolded Un_empty_right PFVars_def, of _ "Abs_SSfun f", unfolded
    Abs_SSfun_inverse[OF iffD2[OF mem_Collect_eq, of "\<lambda>(f::'a::var_terms_pre \<Rightarrow> 'a terms). |SSupp f| <o |UNIV::'a set|", OF assms]]
  ])
  done

lemma nexists_inject: "\<nexists>a. f x = f (g a) \<Longrightarrow> \<nexists>a. x = g a" by blast

lemma not_isVVr_free: "\<not>isVVr (terms_ctor x) \<Longrightarrow> set1_terms_pre x = {}"
  apply (rule \<eta>_compl_free)
  unfolding isVVr_def VVr_def image_iff bex_simps
  apply (rule nexists_inject)
  apply assumption
  done

lemma Union_UN_swap: "\<Union> (\<Union>x\<in>A. P x) = (\<Union>x\<in>A. \<Union>(P x))" by blast
lemma UN_cong: "(\<And>x. x \<in> A \<Longrightarrow> P x = Q x) \<Longrightarrow> \<Union>(P ` A) = \<Union>(Q ` A)" by simp

lemma IImsupp_Diff: "(\<And>x. x \<in> B \<Longrightarrow> x \<notin> IImsupp f) \<Longrightarrow> (\<Union>a\<in>(A - B). FFVars_terms (f a)) = (\<Union>a\<in>A. FFVars_terms (f a)) - B"
  unfolding atomize_imp
  unfolding atomize_all
  apply (drule iffD2[OF disjoint_iff])  apply (rule iffD2[OF set_eq_iff])
  apply (rule allI)
  apply (rule iffI)
   apply (erule UN_E)
   apply (erule DiffE)
   apply (rule DiffI)
    apply (rule UN_I)
     apply assumption
  apply assumption
  subgoal for x a
    apply (rule case_split[of "f a = VVr a"])
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
    apply (rule trans)
      apply (rule arg_cong[of _ _ FFVars_terms])
       apply assumption
      apply (rule FVars_VVr)
     apply (drule singletonD)
     apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply assumption
    apply (drule in_IImsupp)
     apply assumption
    apply (drule trans[OF Int_commute])
    apply (drule iffD1[OF disjoint_iff])
    apply (erule allE)
    apply (erule impE)
     apply assumption
    apply assumption
    done
  apply (erule DiffE)
  apply (erule UN_E)
  apply (rule UN_I)
   apply (rule DiffI)
    apply assumption
  subgoal for x a
    apply (rule case_split[of "f a = VVr a"])
    apply (rotate_tac -2)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
    apply (rule trans)
      apply (rule arg_cong[of _ _ FFVars_terms])
       apply assumption
      apply (rule FVars_VVr)
     apply (drule singletonD)
     apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply assumption
    apply (frule in_IImsupp)
     apply assumption
    apply (drule trans[OF Int_commute])
    apply (drule iffD1[OF disjoint_iff])
    apply (erule allE)
    apply (erule impE)
     prefer 2
     apply assumption
    unfolding IImsupp_def SSupp_def
    apply (rule UnI1)
    apply (rule iffD2[OF mem_Collect_eq])
    apply assumption
    done
  apply assumption
  done

lemma FFVars_tvsubst:
  fixes t::"'a::var_terms_pre terms"
  assumes "|SSupp f| <o |UNIV::'a set|"
  shows "FFVars_terms (tvsubst f t) = (\<Union>a\<in>FFVars_terms t. FFVars_terms (f a))"
  apply (rule terms.TT_fresh_co_induct[of "IImsupp f" _ t])
  apply (unfold IImsupp_def)[1]
    apply (rule terms_pre.Un_bound)
     apply (rule assms)
    apply (rule terms_pre.UNION_bound)
     apply (rule assms)
    apply (rule terms.card_of_FFVars_bounds)
  subgoal for x
    apply (rule case_split[of "isVVr (terms_ctor x)"])
    apply (unfold isVVr_def)[1]
     apply (erule exE)
     apply (rule trans)
      apply (rule arg_cong[of _ _ "\<lambda>x. FFVars_terms (tvsubst f x)"])
      apply assumption
    unfolding tvsubst_VVr[OF assms]
    subgoal premises prems for a
      unfolding prems(6) FVars_VVr UN_single
      apply (rule refl)
      done
    apply (rule trans)
     apply (rule arg_cong[of _ _ FFVars_terms])
     apply (rule tvsubst_cctor_not_isVVr)
        apply (rule assms)
       apply (rule iffD2[OF disjoint_iff])
    apply (rule allI)
       apply (rule impI)
       apply assumption
    unfolding tvnoclash_terms_def Int_Un_distrib Un_empty
      apply (rule conjI)
       apply (rule iffD2[OF disjoint_iff], rule allI, rule impI)
       apply assumption
      apply (rule iffD2[OF disjoint_iff], rule allI, rule impI)
    unfolding UN_iff bex_simps
      apply (rule ballI)
      apply assumption
     apply assumption
    unfolding terms.FFVars_cctors terms_pre.set_map[OF supp_id_bound bij_id supp_id_bound]
      image_id image_comp UN_Un
    apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
      apply (unfold not_isVVr_free UN_empty)
      apply (rule refl)
     apply (rule trans[rotated])
      apply (rule sym)
      apply (rule IImsupp_Diff)
      apply assumption
     apply (rule arg_cong2[OF _ refl, of _ _ "(-)"])
    unfolding UN_simps comp_def
     apply (rule UN_cong)
     apply assumption
    apply (rule UN_cong)
    apply assumption
    done
  done

lemma tvsubst_VVr_func: "tvsubst VVr t = t"
  apply (rule terms.TT_plain_co_induct)
  subgoal for x
    apply (rule case_split[of "isVVr (terms_ctor x)"])
     apply (unfold isVVr_def)[1]
     apply (erule exE)
    subgoal premises prems for a
      unfolding prems
      apply (rule tvsubst_VVr)
      apply (rule SSupp_VVr_bound)
        done
      apply (rule trans)
       apply (rule tvsubst_cctor_not_isVVr)
          apply (rule SSupp_VVr_bound)
      unfolding IImsupp_VVr_empty
         apply (rule Int_empty_right)
      unfolding tvnoclash_terms_def Int_Un_distrib Un_empty
        apply (rule conjI)
         apply (rule iffD2[OF disjoint_iff], rule allI, rule impI, assumption)
        apply (rule iffD2[OF disjoint_iff], rule allI, rule impI)
      unfolding UN_iff bex_simps
        apply (rule ballI)
        apply assumption+
      apply (rule arg_cong[of _ _ terms_ctor])
      apply (rule trans)
      apply (rule terms_pre.map_cong)
                 apply (rule supp_id_bound bij_id)+
           apply (assumption | rule refl)+
      unfolding id_def[symmetric] terms_pre.map_id
      apply (rule refl)
      done
    done

lemma finite_singleton: "finite {x}" by blast
lemma singl_bound: "|{a}| <o |UNIV::'a::var_terms_pre set|"
  by (rule finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite]])

lemma SSupp_upd_bound:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a terms"
  shows "|SSupp (f (a:=t))| <o |UNIV::'a set| \<longleftrightarrow> |SSupp f| <o |UNIV::'a set|"
  unfolding SSupp_def
  apply (auto simp only: fun_upd_apply singl_bound ordLeq_refl split: if_splits
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF terms_pre.Un_bound], rotated]
      intro: card_of_mono1)
  done

corollary SSupp_upd_VVr_bound: "|SSupp (VVr(a:=(t::'a::var_terms_pre terms)))| <o |UNIV::'a set|"
  apply (rule iffD2[OF SSupp_upd_bound])
  apply (rule SSupp_VVr_bound)
  done

(* small step semantics *)
no_notation Set.member  ("(_/ : _)" [51, 51] 50)
no_notation Set.member  ("(_/ \<in> _)" [51, 51] 50)

fun isin :: "'a * 'b \<Rightarrow> ('a * 'b) list \<Rightarrow> bool" ("(_/ \<in> _)" [51, 51] 50) where
  "isin _ [] = False"
| "isin (x, \<tau>) ((y, \<tau>')#ys) = (if x = y then \<tau> = \<tau>' else isin (x, \<tau>) ys)"

definition fresh :: "'a::var_terms_pre \<Rightarrow> ('a * 'b) list \<Rightarrow> bool" ("(_/ \<sharp> _)" [51, 51] 50) where
  "fresh x \<Gamma> \<equiv> x \<notin> set (map fst \<Gamma>)"

lemma not_isin_member: "x \<sharp> \<Gamma> \<Longrightarrow> \<not>((x, \<tau>) \<in> \<Gamma>)"
  by (induction \<Gamma>) (auto simp: fresh_def split!: if_splits)
lemma isin_member: "(x, \<tau>) \<in> \<Gamma> \<Longrightarrow> Set.member x (set (map fst \<Gamma>))"
  by (induction \<Gamma>) (auto split!: if_splits)
lemma isin_rename: "bij f \<Longrightarrow> (f x, \<tau>) \<in> map (map_prod f id) \<Gamma> \<longleftrightarrow> (x, \<tau>) \<in> \<Gamma>"
  by (induction \<Gamma>) (auto split!: if_splits)

inductive Step :: "'a::var_terms_pre terms \<Rightarrow> 'a terms \<Rightarrow> bool" ("_ \<longrightarrow> _" 25) where
  ST_Beta: "App (Abs x \<tau> e) e2 \<longrightarrow> tvsubst (VVr(x:=e2)) e"
| ST_App: "e1 \<longrightarrow> e1' \<Longrightarrow> App e1 e2 \<longrightarrow> App e1' e2"

inductive Ty :: "('a::var_terms_pre * \<tau>) list \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile>\<^sub>t\<^sub>y _ : _") where
  Ty_Var: "(x, \<tau>) \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y Var x : \<tau>"
| Ty_App: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y App e1 e2 : \<tau>\<^sub>2"
| Ty_Abs: "\<lbrakk> x \<sharp> \<Gamma> ; (x, \<tau>)#\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau> e : \<tau> \<rightarrow> \<tau>\<^sub>2"

inductive_cases
  Ty_VarE: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Var x : \<tau>"
  and Ty_AppE: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y App e1 e2 : \<tau>\<^sub>2"
  and Ty_AbsE_aux: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau> e : \<tau>'"

print_theorems

lemma rename_Ty_aux:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>'"
  shows "map (map_prod f id) \<Gamma> \<turnstile>\<^sub>t\<^sub>y rrename_terms f e : \<tau>'"
  apply (rule Ty.induct[OF assms(3)])
  unfolding rrename_simps[OF assms(1,2)]
    apply (rule Ty_Var)
  subgoal for x \<tau> \<Gamma>
    unfolding atomize_imp
    apply (rule list.induct[of _ \<Gamma>])
     apply (rule impI)
    unfolding isin.simps
     apply (erule FalseE)
    apply (rule impI)
    subgoal for y ys
      apply (rule prod.exhaust[of y])
      apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
      subgoal for x' \<tau>'
        apply (rule case_split[of "x = x'"])
         apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
        unfolding list.map map_prod_simp isin.simps bij_implies_inject[OF assms(1)]
         apply (rule iffD2[OF if_P])
          apply (rule refl)
         apply (rule trans[OF _ id_apply[symmetric]])
         apply (drule iffD1[OF if_P, rotated])
          apply (rule refl)
         apply assumption
        unfolding if_not_P
        apply (erule impE)
         apply assumption
        apply assumption
        done
      done
    done
   apply (rule Ty_App)
    apply assumption+
  apply (rule Ty_Abs)
  unfolding fresh_def
  apply (raw_tactic \<open>Ctr_Sugar_Tactics.unfold_thms_tac @{context} (
    BNF_Def.set_map_of_bnf (the (BNF_Def.bnf_of @{context} "List.list"))
  )\<close>)
  unfolding image_comp fst_comp_map_prod[symmetric]
  unfolding image_comp[symmetric] inj_image_mem_iff[OF bij_is_inj[OF assms(1)]]
  apply assumption
  unfolding list.map map_prod_simp id_def
  apply assumption
  done

lemma rename_Ty:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>' \<longleftrightarrow> map (map_prod f id) \<Gamma> \<turnstile>\<^sub>t\<^sub>y rrename_terms f e : \<tau>'"
  apply (rule iffI)
   apply (rule rename_Ty_aux)
     apply (rule assms)+
   apply assumption
  apply (drule rename_Ty_aux[rotated -1])
    apply (rule bij_imp_bij_inv)
    apply (rule assms)
   apply (rule supp_inv_bound)
    apply (rule assms)+
  unfolding terms.rrename_comps[OF assms bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]]
    inv_o_simp1[OF assms(1)] terms.rrename_ids list.map_comp map_prod.comp id_o map_prod.id list.map_id
  apply assumption
  done

lemma context_invariance: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>' \<Longrightarrow> \<forall>x\<in>FFVars_terms e. \<forall>\<tau>. (x, \<tau>) \<in> \<Gamma> \<longrightarrow> (x, \<tau>) \<in> \<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>t\<^sub>y e : \<tau>'"
proof (induction e arbitrary: \<Gamma> \<Gamma>' \<tau>' rule: TT_fresh_induct[of "{}"])
  case Bound
  then show ?case by (rule emp_bound)
next
  case (Var a)
  then show ?case unfolding FFVars_terms_simps using Ty_Var Ty_VarE by blast
next
  case (App e1 e2)
  then obtain \<tau>1 where "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>1 \<rightarrow> \<tau>'" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>1" using Ty_AppE by blast
  then have "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>1 \<rightarrow> \<tau>'" "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>1" using App by auto
  then show ?case by (rule Ty_App)
next
  case (Abs x \<tau> e)
  from Abs(3) obtain x' e' \<tau>2 f where x: "\<tau>' = (\<tau> \<rightarrow> \<tau>2)" "Abs x \<tau> e = Abs x' \<tau> e'" "(x', \<tau>)#\<Gamma> \<turnstile>\<^sub>t\<^sub>y e' : \<tau>2" "f x = x'"
    "rrename_terms f e = e'" "bij (f::'a::var_terms_pre \<Rightarrow> 'a)" "|supp f| <o |UNIV::'a set|" "id_on (FFVars_terms (Abs x \<tau> e)) f"
    "x' \<sharp> \<Gamma>"
    by (smt (verit, best) Abs_inject Ty_AbsE_aux)
  then have 1: "(f x, \<tau>)#\<Gamma> \<turnstile>\<^sub>t\<^sub>y rrename_terms f e : \<tau>2" by simp
  have 2: "(x, \<tau>) # map (map_prod (inv f) id) \<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>2"
    apply (rule iffD2[OF rename_Ty[OF x(6,7)]])
    unfolding list.map map_prod_simp list.map_comp map_prod.comp id_o inv_o_simp2[OF x(6)] map_prod.id list.map_id
    unfolding id_def
    apply (rule 1)
    done
  have 3: "\<forall>xa\<in>FFVars_terms e. \<forall>\<tau>'. (xa, \<tau>') \<in> (x, \<tau>) # map (map_prod (inv f) id) \<Gamma> \<longrightarrow> (xa, \<tau>') \<in> (x, \<tau>) # map (map_prod (inv f) id) \<Gamma>'"
  proof (rule ballI, rule allI, rule impI)
    fix y \<sigma>
    assume a: "Set.member y (FFVars_terms e)" "(y, \<sigma>) \<in> (x, \<tau>) # map (map_prod (inv f) id) \<Gamma>"
    have y1: "(f y, \<sigma>) \<in> (f x, \<tau>)#\<Gamma>"
      using iffD2[OF isin_rename[OF x(6)] a(2),
          unfolded list.map list.map_comp map_prod.comp id_o inv_o_simp2[OF x(6)] map_prod.id list.map_id map_prod_simp,
          unfolded id_def] .
    show "(y, \<sigma>) \<in> (x, \<tau>) # map (map_prod (inv f) id) \<Gamma>'"
    proof (cases "x = y")
      case True
      then show ?thesis using a by simp
    next
      case False
      then have y2: "f y = y" using x(8) a(1) unfolding id_on_def by simp
      from False have y3: "(f y, \<sigma>) \<in> \<Gamma>" using bij_implies_inject[OF x(6)] y1 by simp
      then have "(y, \<sigma>) \<in> \<Gamma>'" using y2 Abs(4) False a by simp
      then have "(y, \<sigma>) \<in> map (map_prod (inv f) id) \<Gamma>'" using isin_rename[OF bij_imp_bij_inv[OF x(6)]] y2 x(6)
        by (smt (verit) bij_betw_def inv_f_eq) 
      then show ?thesis using False by simp
    qed
  qed
  then have y4: "(x, \<tau>) # map (map_prod (inv f) id) \<Gamma>' \<turnstile>\<^sub>t\<^sub>y e : \<tau>2" using Abs(2) 2 by blast
  have "(x', \<tau>) # \<Gamma>' \<turnstile>\<^sub>t\<^sub>y e' : \<tau>2"
    unfolding x(4,5)[symmetric]
    apply (rule iffD2[OF rename_Ty[OF bij_imp_bij_inv supp_inv_bound]])
       apply (rule x(6,7))+
    unfolding list.map map_prod_simp inv_simp1[OF x(6)] inv_o_simp1[OF x(6)] terms.rrename_ids
      terms.rrename_comps[OF x(6,7) bij_imp_bij_inv[OF x(6)] supp_inv_bound[OF x(6,7)]]
    unfolding id_def
    apply (rule y4[unfolded id_def])
    done
  then show ?case using x(1,2,9) sorry
qed

lemma Ty_AbsE:
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau> e : \<tau>'"
  and "\<And>\<tau>2. \<tau>' = (\<tau> \<rightarrow> \<tau>2) \<Longrightarrow> (x, \<tau>) # \<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>2 \<Longrightarrow> P"
shows P
proof -
  obtain x' e' \<tau>2 f where x: "Abs x \<tau> e = Abs x' \<tau> e'" "(x', \<tau>) # \<Gamma> \<turnstile>\<^sub>t\<^sub>y e' : \<tau>2" "f x = x'" "rrename_terms f e = e'"
    "bij (f::'a::var_terms_pre \<Rightarrow> 'a)" "|supp f| <o |UNIV::'a set|" "id_on (FFVars_terms (Abs x \<tau> e)) f" "x' \<sharp> \<Gamma>"
    using Ty_AbsE_aux[OF assms(1)] Abs_inject by (smt (verit, best))

  obtain \<Gamma>' where "\<forall>y\<in>FFVars_terms e. \<forall>\<tau>. (y, \<tau>) \<in> \<Gamma> \<longleftrightarrow> (y, \<tau>) \<in> \<Gamma>'" by blast
  then have "set (map fst \<Gamma>') \<subseteq> FFVars_terms e"
    apply (induction \<Gamma>') apply (auto split!: if_splits)
    sorry

  show ?thesis sorry
qed

lemma Ty_induct[consumes 1, case_names Bound Var App Abs]:
  fixes e::"'a::var_terms_pre terms" and A::"'a set"
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>"
  and Bound: "|A| <o |UNIV::'a set|"
  and Var: "\<And>x \<tau> \<Gamma>. (x, \<tau>) \<in> \<Gamma> \<Longrightarrow> P \<Gamma> (Var x) \<tau>"
  and App: "\<And>\<Gamma> e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2. \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 \<Longrightarrow> P \<Gamma> e1 (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1 \<Longrightarrow> P \<Gamma> e2 \<tau>\<^sub>1 \<Longrightarrow> P \<Gamma> (App e1 e2) \<tau>\<^sub>2"
  and Abs: "\<And>x \<Gamma> \<tau> e \<tau>\<^sub>2. x \<notin> A \<Longrightarrow> x \<sharp> \<Gamma> \<Longrightarrow> (x, \<tau>) # \<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<Longrightarrow> P ((x, \<tau>) # \<Gamma>) e \<tau>\<^sub>2 \<Longrightarrow> P \<Gamma> (Abs x \<tau> e) (\<tau> \<rightarrow> \<tau>\<^sub>2)"
shows "P \<Gamma> e \<tau>"
  apply (rule Ty.induct)
     apply (rule assms(1))
    apply (rule Var)
    apply assumption
   apply (rule App)
      apply assumption+
  subgoal for x \<Gamma> \<tau> e \<tau>2

(*
    apply (rule exE[OF Abs_avoid[of _ x \<tau> e]])
     apply (rule terms.Un_bound)
      apply (rule Bound)
    apply (rule ordLess_ordLeq_trans)
    apply (raw_tactic \<open>resolve_tac @{context} (
      BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "List.list"))
    ) 1\<close>)
    unfolding Un_iff de_Morgan_disj
    apply (rule terms_pre.var_large)
    apply (erule exE conjE)+
    apply (rule iffD2[OF arg_cong3[OF refl _ refl, of _ _ P]])
     apply assumption
    unfolding Abs_inject
    apply (erule exE conjE)+
    apply (rule iffD2[OF arg_cong3[OF _ refl refl, of _ _ P]])
    defer
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule Abs)
       apply assumption
    unfolding fresh_def
      apply assumption
    unfolding fresh_def[symmetric]
     apply (drule rename_Ty[rotated -1])
       apply assumption+
    unfolding list.map map_prod_simp id_def
    unfolding id_def[symmetric]
*)



theorem progress: "[] \<turnstile>\<^sub>t\<^sub>y e : \<tau> \<Longrightarrow> (\<exists>x \<tau> e'. e = Abs x \<tau> e') \<or> (\<exists>e'. e \<longrightarrow> e')"
proof (induction "[] :: ('a::var_terms_pre * \<tau>) list" e \<tau> rule: Ty.induct)
  case (Ty_App e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2)
  from Ty_App(2) show ?case using ST_Beta ST_App by blast
qed auto

lemma context_invariance: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau> ; \<forall>x \<tau>'. (x, \<tau>') \<in> \<Gamma> \<longrightarrow> (x, \<tau>') \<in> \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>t\<^sub>y e : \<tau>"
proof (induction \<Gamma> e \<tau> arbitrary: \<Gamma>' rule: Ty.induct)
  case (Ty_Abs x \<Gamma> \<tau> e \<tau>\<^sub>2)
  then have "\<forall>x' \<tau>'. (x', \<tau>') \<in> (x, \<tau>)#\<Gamma> \<longrightarrow> (x', \<tau>') \<in> (x, \<tau>)#\<Gamma>'" by auto
  then show ?case using Ty_Abs Ty.Ty_Abs by blast
qed (auto intro: Ty_Var Ty_App)

lemma substitution: "\<lbrakk> (x, \<tau>')#\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau> ; [] \<turnstile>\<^sub>t\<^sub>y v : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x:=v)) e : \<tau>"
proof (induction e arbitrary: \<Gamma> \<tau> rule: TT_fresh_induct[of "{x} \<union> FFVars_terms v"])
  case Bound
  then show ?case using terms_pre.Un_bound singl_bound terms.card_of_FFVars_bounds by fast
next
  case (Var a)
  then have 2: "(a, \<tau>) \<in> (x, \<tau>') # \<Gamma>" by cases auto
  have 3: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y v : \<tau>'" using context_invariance[OF Var(2)] by simp
  then show ?case unfolding tvsubst_simps[OF SSupp_upd_VVr_bound] unfolding fun_upd_def
  proof (cases "a = x")
    case True
    then have "\<tau> = \<tau>'" using 2 by simp
    then show "\<Gamma> \<turnstile>\<^sub>t\<^sub>y if a = x then v else VVr a : \<tau>" using True 3 by simp
  next
    case False
    then have 4: "(a, \<tau>) \<in> \<Gamma>" using 2 by simp
    show "\<Gamma> \<turnstile>\<^sub>t\<^sub>y if a = x then v else VVr a : \<tau>" unfolding VVr_eq_Var using False Ty.Ty_Var[OF 4] by simp
  qed
next
  case (App e1 e2)
  from App(3) obtain \<tau>1 where "(x, \<tau>') # \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>1 \<rightarrow> \<tau>" "(x, \<tau>') # \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>1" by cases auto
  then have "\<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := v)) e1 : \<tau>1 \<rightarrow> \<tau>" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := v)) e2 : \<tau>1" using App by blast+
  then have "\<Gamma> \<turnstile>\<^sub>t\<^sub>y App (tvsubst (VVr(x := v)) e1) (tvsubst (VVr(x := v)) e2) : \<tau>" using Ty_App by blast
  then show ?case unfolding tvsubst_simps(2)[OF SSupp_upd_VVr_bound, symmetric] .
next
  case (Abs y \<tau>1 e)
  then have 1: "y \<notin> IImsupp (VVr(x:=v))" by (simp add: IImsupp_def SSupp_def)
  from Abs(3) have "\<exists>y' e' \<tau>2. (y', \<tau>1)#(x, \<tau>')#\<Gamma> \<turnstile>\<^sub>t\<^sub>y e' : \<tau>2 \<and> Abs y \<tau>' e = Abs y' \<tau>' e' \<and> y' \<noteq> x \<and> \<tau> = (\<tau>1 \<rightarrow> \<tau>2)"
  proof cases
    case (Ty_Abs y' \<tau>1' e' \<tau>\<^sub>2)
    then obtain y'' e'' where "Abs y \<tau>1 e = Abs y'' \<tau>1 e''" "y'' \<noteq> x" using Abs_avoid[OF singl_bound[of x]] by blast
    then show ?thesis using Ty_Abs sorry
  qed auto
  
  show ?case unfolding tvsubst_simps(3)[OF SSupp_upd_VVr_bound 1] using Abs sorry
qed

theorem preservation: "\<lbrakk> [] \<turnstile>\<^sub>t\<^sub>y e : \<tau> ; e \<longrightarrow> e' \<rbrakk> \<Longrightarrow> [] \<turnstile>\<^sub>t\<^sub>y e' : \<tau>"
proof (induction "[] :: ('a::var_terms_pre * \<tau>) list" e \<tau> arbitrary: e' rule: Ty.induct)
  case (Ty_App e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2)
  from Ty_App(5) show ?case
  proof cases
    case (ST_Beta x \<tau> e e2')
    then have "[] \<turnstile>\<^sub>t\<^sub>y App (Abs x \<tau> e) e2 : \<tau>\<^sub>2" using Ty_App Ty.Ty_App by fastforce
    then have "[] \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := e2)) e : \<tau>\<^sub>2" using Ty_App sorry
    then show ?thesis using ST_Beta by simp
  next
    case (ST_App e e1' e2')
    then have "[] \<turnstile>\<^sub>t\<^sub>y e1' : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2" using Ty_App by simp
    then show ?thesis using Ty_App Ty.Ty_App ST_App by fastforce
  qed
next
  case (Ty_Abs x \<tau> e \<tau>\<^sub>2)
  from Ty_Abs(2) show ?case by cases auto
qed auto

end