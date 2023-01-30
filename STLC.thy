theory STLC
  imports "thys/MRBNF_Recursor" "HOL-Library.FSet"
begin

datatype \<tau> = Unit | Arrow \<tau> \<tau> (infixr "\<rightarrow>" 40)

(* binder_datatype 'a terms =
  Var 'a
| App "'a terms" "'a terms"
| Abs x::'a \<tau> t::"'a terms" binds x in t
*)

ML \<open>
val name = "terms"
val T = @{typ "'var + 'rec * 'rec + 'bvar * \<tau> * 'brec"}
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

  (* Step 5: Create recursor and create fixpoint as MRBNF *)
  val (rec_mrbnf, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint @{binding vvsubst} I (hd res) lthy;

  (* Step 6: Register fixpoint MRBNF *)
  val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (#quotient_fp (hd res))))) rec_mrbnf lthy;
in lthy end
\<close>
print_theorems
print_mrbnfs

lemma UN_single: "\<Union>(f ` {a}) = f a" by simp

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

(* Term for variable substitution *)
(* TODO: Define with ML *)
definition \<eta> :: "'a::var_terms_pre \<Rightarrow> ('a, 'b::var_terms_pre, 'c, 'd) terms_pre" where
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
lemma not_fun_cong: "f a \<noteq> f b \<Longrightarrow> a \<noteq> b" by blast
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
lemma forall_in_eq_UNIV: "\<forall>c. (c::'a) \<in> X \<Longrightarrow> X = (UNIV :: 'a set)" by blast
lemma image_const: "a \<in> X \<Longrightarrow> \<forall>c. c \<in> (\<lambda>_. c) ` X" by simp
lemma ordIso_ordLess_False: "a =o b \<Longrightarrow> a <o b \<Longrightarrow> False"
  by (simp add: not_ordLess_ordIso)

(* eta axioms *)
lemma \<eta>_free: "set1_terms_pre (\<eta> a) = {a}"
  unfolding set1_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] \<eta>_def
  by auto
lemma \<eta>_inj: "\<eta> a = \<eta> b \<Longrightarrow> a = b"
  unfolding Abs_terms_pre_inject[OF UNIV_I UNIV_I] sum.inject  \<eta>_def
  by assumption
lemma \<eta>_compl_free: "x \<notin> range \<eta> \<Longrightarrow> set1_terms_pre x = {}"
  unfolding set1_terms_pre_def comp_def Un_empty sum.set_map UN_singleton UN_empty2  \<eta>_def
  apply (rule conjI)
   apply (rule Abs_terms_pre_cases[of x])
   apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding Abs_terms_pre_inverse[OF UNIV_I] Abs_terms_pre_inject[OF UNIV_I UNIV_I] image_iff bex_UNIV
   apply ((rule nexists_setl, assumption) | rule refl)+
  done
lemma \<eta>_natural: "|supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij g \<Longrightarrow> |supp (g::'b::var_terms_pre \<Rightarrow> 'b)| <o |UNIV::'b set|
  \<Longrightarrow> map_terms_pre f g h i \<circ> \<eta> = \<eta> \<circ> f"
  unfolding comp_def map_terms_pre_def Abs_terms_pre_inverse[OF UNIV_I] map_sum.simps  \<eta>_def
  apply (rule refl)
  done

ML_file \<open>Tools/mrbnf_tvsubst.ML\<close>

declare [[ML_print_depth=1000]]
ML \<open>
Multithreading.parallel_proofs := 0
\<close>
local_setup \<open>fn lthy =>
let
  val fp_result = the (MRBNF_FP_Def_Sugar.fp_result_of lthy "STLC.terms")

  val axioms = {
    eta_free = fn ctxt => resolve_tac ctxt @{thms \<eta>_free} 1,
    eta_inj = fn ctxt => resolve_tac ctxt @{thms \<eta>_inj} 1 THEN assume_tac ctxt 1,
    eta_compl_free = fn ctxt => resolve_tac ctxt @{thms \<eta>_compl_free} 1 THEN assume_tac ctxt 1,
    eta_natural = fn ctxt => resolve_tac ctxt @{thms \<eta>_natural} 1 THEN ALLGOALS (assume_tac ctxt)
  };

  val model = {
    fp_result = fp_result,
    etas = [SOME (
      @{term "\<eta>::'a::var_terms_pre \<Rightarrow> ('a, 'b::var_terms_pre, 'c, 'd) terms_pre"},
      axioms
    )]
  };
  val lthy = MRBNF_TVSubst.create_tvsubst_of_mrbnf @{binding tvsubst} (Binding.prefix_name "tv") model lthy
in lthy end
\<close>
print_theorems

(* after recursor *)
lemma not_isVVr_free: "\<not>isVVr (terms_ctor x) \<Longrightarrow> set1_terms_pre x = {}"
  apply (rule \<eta>_compl_free)
  unfolding isVVr_def VVr_def image_iff Set.bex_simps not_ex comp_def
  apply (rule allI)
  apply (erule allE)
  apply (rule not_fun_cong)
  apply assumption
  done

lemma Union_UN_swap: "\<Union> (\<Union>x\<in>A. P x) = (\<Union>x\<in>A. \<Union>(P x))" by blast
lemma UN_cong: "(\<And>x. x \<in> A \<Longrightarrow> P x = Q x) \<Longrightarrow> \<Union>(P ` A) = \<Union>(Q ` A)" by simp

lemma IImsupp_Diff: "(\<And>x. x \<in> B \<Longrightarrow> x \<notin> IImsupp f) \<Longrightarrow> (\<Union>a\<in>(A - B). FFVars_terms (f a)) = (\<Union>a\<in>A. FFVars_terms (f a)) - B"
  unfolding atomize_imp
  unfolding atomize_all
  apply (drule iffD2[OF disjoint_iff])
  apply (rule iffD2[OF set_eq_iff])
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
  apply (unfold IImsupp_def comp_def)[1]
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
     apply (rule sym)
     apply (rule trans)
      apply (rule arg_cong[of _ _ "\<lambda>x. \<Union>(_ ` x)"])
      apply (rule arg_cong[of _ _ FFVars_terms])
      apply assumption
     apply (unfold FVars_VVr UN_single)
     apply (rule refl)

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
    unfolding UN_iff Set.bex_simps
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

lemma IImsupp_VVr_empty: "IImsupp VVr = {}"
  unfolding IImsupp_def SSupp_VVr_empty UN_empty Un_empty_left
  apply (rule refl)
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
      unfolding UN_iff Set.bex_simps
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

lemma supp_subset_id_on: "supp f \<subseteq> A \<Longrightarrow> id_on (B - A) f"
  unfolding supp_def id_on_def by blast

(* Nice syntax for binder datatypes *)
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

lemma TT_fresh_induct_param[case_names Bound Var App Abs]:
  fixes x::"'a::var_terms_pre terms" and K::"'b \<Rightarrow> 'a set"
  assumes "\<forall>\<rho>. |K \<rho>| <o |UNIV::'a set|"
and Var: "\<And>a \<rho>. P (Var a) \<rho>"
and App: "\<And>e1 e2 \<rho>. \<lbrakk> \<forall>\<rho>. P e1 \<rho> ; \<forall>\<rho>. P e2 \<rho> \<rbrakk> \<Longrightarrow> P (App e1 e2) \<rho>"
and Abs: "\<And>x \<tau> e \<rho>. \<lbrakk> x \<notin> K \<rho> ; \<forall>\<rho>. P e \<rho> \<rbrakk> \<Longrightarrow> P (Abs x \<tau> e) \<rho>"
shows "\<forall>\<rho>. P x \<rho>"
  apply (rule allI)
  subgoal for \<rho>
  apply (rule spec[OF terms.TT_fresh_co_induct_param[of "UNIV::'b set", unfolded ball_UNIV, of K]])
   apply (rule spec[OF assms(1)])
  subgoal premises IHs for v \<rho>
    apply (rule Abs_terms_pre_cases[of v])
    subgoal for y
      apply (rule sum.exhaust[of y])
       apply hypsubst
      apply (rule Var[unfolded Var_def])
      subgoal for y2
        apply (rule sum.exhaust[of y2])
        subgoal for y3
          apply (rule prod.exhaust[of y3])
          apply hypsubst
          apply (frule arg_cong[of _ _ "Abs_terms_pre"])
        apply (rotate_tac -1)
          apply (drule arg_cong[of _ _ terms_ctor])
          unfolding App_def[symmetric]
          apply (drule App_set4)
          apply (erule conjE)
          apply (rule App)
           apply (rule allI)
           apply (rule IHs(2))
            apply hypsubst
            apply assumption
           apply (rule UNIV_I)
          apply (rule allI)
          apply (rule IHs(2))
           apply hypsubst
           apply assumption
          apply (rule UNIV_I)
          done
        subgoal for y3
          apply (rule prod.exhaust[of y3])
          apply hypsubst
          subgoal for x y4
            apply (rule prod.exhaust[of y4])
            apply hypsubst
            apply (frule arg_cong[of _ _ terms_ctor])
            unfolding Abs_def[symmetric]
            apply (frule Abs_set3)
            apply (erule exE conjE)+
            apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ P]])
            apply (rule trans)
             apply (rule sym)
              apply assumption
             apply (rotate_tac -3)
             apply assumption
            apply (rule Abs)
             apply (rule IHs)
             apply assumption
            apply (rule allI)
            apply (rule IHs(1))
             apply assumption
            apply (rule UNIV_I)
            done
          done
        done
      done
    done
  done
  done

lemma TT_fresh_induct[case_names Bound Var App Abs]:
  assumes bound: "|A::'a set| <o |UNIV::'a::var_terms_pre set|"
  and Var: "\<And>a. P (Var a)"
  and App: "\<And>e1 e2. P e1 \<Longrightarrow> P e2 \<Longrightarrow> P (App e1 e2)"
  and Abs: "\<And>x \<tau> e. x \<notin> A \<Longrightarrow> P e \<Longrightarrow> P (Abs x \<tau> e)"
shows "P x"
  apply (rule spec[OF TT_fresh_induct_param[of _ "\<lambda>x \<rho>. P x"]])
     apply (rule allI)
     apply (rule assms | assumption | erule allE)+
  done

lemmas TT_plain_induct = TT_fresh_induct[OF emp_bound, case_names Var App Abs]

lemma tvsubst_Var: "|SSupp (f::'a::var_terms_pre \<Rightarrow> 'a terms)| <o |UNIV::'a set| \<Longrightarrow> tvsubst f (Var x) = f x"
  unfolding Var_def fun_cong[OF meta_eq_to_obj_eq[OF VVr_def[unfolded comp_def \<eta>_def, symmetric]]]
  apply (rule tvsubst_VVr)
  apply assumption
  done

lemma VVr_eq_Var: "VVr a = Var a"
  unfolding VVr_def Var_def comp_def \<eta>_def
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
  unfolding \<eta>_def[symmetric] \<eta>_set2 noclash_terms_def fun_cong[OF \<eta>_natural[OF _ bij_id supp_id_bound], unfolded comp_def]
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

(* small step semantics *)
no_notation Set.member  ("(_/ : _)" [51, 51] 50)

definition fresh :: "'a::var_terms_pre \<Rightarrow> ('a * 'b) fset \<Rightarrow> bool" ("(_/ \<sharp> _)" [51, 51] 50) where
  "fresh x \<Gamma> \<equiv> x |\<notin>| fst |`| \<Gamma>"

lemma isin_rename: "bij f \<Longrightarrow> (f x, \<tau>) |\<in>| map_prod f id |`| \<Gamma> \<longleftrightarrow> (x, \<tau>) |\<in>| \<Gamma>"
  by force

abbreviation extend :: "('a * \<tau>) fset \<Rightarrow> 'a::var_terms_pre \<Rightarrow> \<tau> \<Rightarrow> ('a * \<tau>) fset" ("(_,_:_)" [52, 52, 52] 53) where
  "extend \<Gamma> a \<tau> \<equiv> finsert (a, \<tau>) \<Gamma>"

inductive Step :: "'a::var_terms_pre terms \<Rightarrow> 'a terms \<Rightarrow> bool" ("_ \<longrightarrow> _" 25) where
  ST_Beta: "App (Abs x \<tau> e) e2 \<longrightarrow> tvsubst (VVr(x:=e2)) e"
| ST_App: "e1 \<longrightarrow> e1' \<Longrightarrow> App e1 e2 \<longrightarrow> App e1' e2"

inductive Ty :: "('a::var_terms_pre * \<tau>) fset \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile>\<^sub>t\<^sub>y _ : _") where
  Ty_Var: "(x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y Var x : \<tau>"
| Ty_App: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y App e1 e2 : \<tau>\<^sub>2"
| Ty_Abs: "\<lbrakk> x \<sharp> \<Gamma> ; \<Gamma>,x:\<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau> e : \<tau> \<rightarrow> \<tau>\<^sub>2"

(* Design for better inductive:

provide additional command `binder_inductive` that takes the name of a normal inductive as argument.
This uses the map function of the BNFs involved.

binder_inductive Ty where
  Ty_Abs: x

This opens a proof for all the equalities and implications needed: *)

lemma provided:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows
    (* equivariance *)
    "(x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> (f x, \<tau>) |\<in>| map_prod f id |`| \<Gamma>"
    "x \<sharp> \<Gamma> \<Longrightarrow> f x \<sharp> map_prod f id |`| \<Gamma>"
    (* equivariance of extend *)
    "map_prod f id |`| (\<Gamma>,x:\<tau>) = (map_prod f id |`| \<Gamma>),f x:\<tau>"
    (* freshness *)
    "\<lbrakk> x \<sharp> \<Gamma> ; \<Gamma>,x:\<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<rbrakk> \<Longrightarrow> x \<notin> \<Union>(Basic_BNFs.fsts ` fset \<Gamma>)"
   apply (simp add: assms isin_rename)
  unfolding fresh_def
  apply (metis Product_Type.fst_comp_map_prod assms(1) bij_not_equal_iff fimageE fset.map_comp)
   apply simp
  using fmember.rep_eq image_iff apply fastforce
  done

lemma rename_Ty_aux:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes
    "bij f" "|supp f| <o |UNIV::'a set|" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>'"
  shows "map_prod f id |`| \<Gamma> \<turnstile>\<^sub>t\<^sub>y vvsubst f e : \<tau>'"
  apply (rule Ty.induct[OF assms(3)])
  unfolding terms_vvsubst_rrename[OF assms(1,2)] rrename_simps[OF assms(1,2)]
    apply (rule Ty_Var)
    apply (rule provided)
      apply (rule assms)+
  apply assumption
   apply (rule Ty_App)
    apply assumption+
  apply (rule Ty_Abs)
   apply (rule provided)
     apply (rule assms)+
   apply assumption
  unfolding provided[OF assms(1,2)]
  apply assumption
  done

lemma rename_Ty:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>' \<longleftrightarrow> map_prod f id |`| \<Gamma> \<turnstile>\<^sub>t\<^sub>y vvsubst f e : \<tau>'"
  apply (rule iffI)
   apply (rule rename_Ty_aux)
     apply (rule assms)+
   apply assumption
  apply (drule rename_Ty_aux[rotated -1])
    apply (rule bij_imp_bij_inv)
    apply (rule assms)
   apply (rule supp_inv_bound)
    apply (rule assms)+
  unfolding terms.map_comp[OF assms(2) supp_inv_bound[OF assms]]
    inv_o_simp1[OF assms(1)] terms.map_id map_prod.comp id_o map_prod.id fset.map_comp fset.map_id
  apply assumption
  done

definition cl :: "(('a::var_terms_pre \<times> \<tau>) fset \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> \<tau>) fset \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> 'b \<Rightarrow> bool" where
  "cl P \<Gamma> e \<tau> \<rho> \<equiv> (\<forall>f. bij f \<and> |supp f| <o |UNIV::'a set| \<longrightarrow> P (map_prod f id |`| \<Gamma>) (vvsubst f e) \<tau> \<rho>)"

lemmas clI = allI[THEN iffD2[OF meta_eq_to_obj_eq[OF cl_def]], unfolded atomize_imp[symmetric]]

lemma clD:
  fixes e::"'a::var_terms_pre terms" and f::"'a \<Rightarrow> 'a"
assumes "cl P \<Gamma> e \<tau> \<rho>" and "bij f" "|supp f| <o |UNIV::'a set|"
shows "P (map_prod f id |`| \<Gamma>) (vvsubst f e) \<tau> \<rho>"
  apply (rule mp[OF spec[OF assms(1)[unfolded cl_def]]])
  apply (rule conjI)
   apply (rule assms)+
  done

lemma cl_ext: "cl P \<Gamma> e \<tau> \<rho> \<Longrightarrow> P \<Gamma> e \<tau> \<rho>"
  unfolding cl_def
  apply (erule allE)
  apply (erule impE)
   apply (rule conjI)
    apply (rule bij_id)
   apply (rule supp_id_bound)
  unfolding map_prod.id fset.map_id terms.map_id
  apply assumption
  done

lemma cl_vvsubst:
  fixes e::"'a::var_terms_pre terms"
  assumes f: "bij f" "|supp f| <o |UNIV::'a set|" and cl: "cl P \<Gamma> e \<tau> \<rho>"
  shows "cl P (map_prod f id |`| \<Gamma>) (vvsubst f e) \<tau> \<rho>"
  unfolding cl_def
  apply (rule allI impI)+
  apply (erule conjE)
  unfolding fset.map_comp terms.map_comp[OF f(2)] map_prod.comp id_o
  apply (rule clD[OF cl])
   apply (rule bij_comp)
    apply (rule f)
   apply assumption
  apply (rule supp_comp_bound)
    apply (rule f)
   apply assumption
  apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
  done

lemma cl_cl: "cl (cl P) = cl P"
  unfolding cl_def
  apply (rule ext)+
  apply (rule iffI)
   apply (rule allI)
   apply (rule impI)
   apply (erule allE)
   apply (erule conjE)
   apply (erule impE)
    apply (rule conjI)
     apply assumption+
   apply (erule allE)
   apply (erule impE)
    apply (rule conjI)
     apply (rule bij_id)
    apply (rule supp_id_bound)
  unfolding map_prod.id fset.map_id terms.map_id
   apply assumption
  apply (rule allI impI)+
  apply (erule allE conjE)+
  apply (erule impE)
   defer
  unfolding fset.map_comp map_prod.comp id_o terms.map_comp
   apply assumption
  apply (rule conjI)
   apply (rule bij_comp)
    apply assumption+
  apply (rule supp_comp_bound)
    apply assumption+
  apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
  done

lemma TT_inject: "(terms_ctor a = terms_ctor b) = (\<exists>(f::'a::var_terms_pre \<Rightarrow> 'a). bij f \<and> |supp f| <o |UNIV::'a set|
  \<and> id_on (\<Union>(FFVars_terms ` set3_terms_pre a) - set2_terms_pre a) f \<and> map_terms_pre id f (vvsubst f) id a = b)"
  unfolding terms.TT_injects0 conj_assoc[symmetric]
  apply (rule ex_cong)
  apply (erule conjE)+
  unfolding terms_vvsubst_rrename
  apply (rule refl)
  done

(*no_notation extend ("(_,_:_)")*)

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

lemma id_on_empty: "id_on {} f"
  unfolding id_on_def by simp
lemma disjoint_single: "{x} \<inter> A = {} \<longleftrightarrow> x \<notin> A"
  by simp

lemma Ty_fresh_induct_param[consumes 1, case_names Bound Ty_Var Ty_App Ty_Abs]:
  fixes K::"'p \<Rightarrow> 'a::var_terms_pre set" and e::"'a terms"
  assumes x: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>" and bound: "\<forall>\<rho>. |K \<rho>| <o |UNIV::'a set|"
    and Ty_Var: "\<And>x \<tau> \<Gamma> \<rho>. (x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> P \<Gamma> (Var x) \<tau> \<rho>"
    and Ty_App: "\<And>\<Gamma> e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2 \<rho>. \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 \<Longrightarrow> \<forall>\<rho>. P \<Gamma> e1 (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2) \<rho>
      \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1 \<Longrightarrow> \<forall>\<rho>. P \<Gamma> e2 \<tau>\<^sub>1 \<rho> \<Longrightarrow> P \<Gamma> (App e1 e2) \<tau>\<^sub>2 \<rho>"
    and Ty_Abs: "\<And>x \<Gamma> \<tau> e \<tau>\<^sub>2 \<rho>. x \<notin> K \<rho> \<Longrightarrow> x \<sharp> \<Gamma> \<Longrightarrow> extend \<Gamma> x \<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<Longrightarrow> \<forall>\<rho>. P (extend \<Gamma> x \<tau>) e \<tau>\<^sub>2 \<rho> \<Longrightarrow> P \<Gamma> (Abs x \<tau> e) (\<tau> \<rightarrow> \<tau>\<^sub>2) \<rho>"
  shows "\<forall>\<rho>. P \<Gamma> e \<tau> \<rho>"
  apply (rule allI)
  apply (rule cl_ext[of P])
  apply (rule spec[OF Ty.induct[OF x, of "\<lambda>\<Gamma> e \<tau>. \<forall>\<rho>. cl P \<Gamma> e \<tau> \<rho>"]])

  (* Nonbinding case *)
    apply (rule allI)
    apply (rule clI)
    apply (erule conjE)
  unfolding vvsubst_simps
    apply (rule Ty_Var)
    apply (rule provided)
      apply assumption+
  (* And again *)
  apply (rule allI)
   apply (rule clI)
   apply (erule conjE)
  unfolding vvsubst_simps
   apply (rule Ty_App)
      apply (assumption | (rule allI, (erule allE)+, rule clD[of P]) | rule iffD1[OF rename_Ty])+
  (* binding case *)
  subgoal for \<rho> x \<Gamma> \<tau> e \<tau>2
  apply (rule allI)
  apply (rule clI[of P])
    apply (erule conjE)
    subgoal for \<rho> f
      apply (rule exE[OF Abs_avoid])
       apply (rule terms_pre.Un_bound)
      apply (rule terms_pre.Un_bound)
        apply (rule iffD2[OF imsupp_supp_bound[OF cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite]]])
        apply assumption
        apply (rule spec[OF bound])
       apply (rule terms_pre.UNION_bound)
      apply (rule ordLess_ordLeq_trans[of "|fset \<Gamma>|"])
apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
        apply (rule terms.var_large)
       apply (rule ordLess_ordLeq_trans[of "|Basic_BNFs.fsts _|"])
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
      apply (rule terms.var_large)
     apply (erule exE conjE)+

       apply (rule iffD2[OF fun_cong[of _ _ \<rho>]])
        apply (rule arg_cong3[OF refl _ refl, of _ _ P])
        apply (rule arg_cong2[OF refl, of _ _ vvsubst])
        apply assumption
      unfolding Un_iff de_Morgan_disj
       apply (erule conjE)+
      unfolding vvsubst_simps
       apply (rule Ty_Abs)
          apply assumption
         apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ fresh]])
          apply (rule not_in_imsupp_same[symmetric])
          apply assumption
         apply (rule provided)
          apply assumption+

        apply (unfold Abs_inject)[1]
        apply (erule exE conjE)+
        apply hypsubst
        apply (rule exE[OF ex_avoiding_bij])
                apply (rotate_tac -3)
                apply assumption
               apply assumption
              apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
             apply (rule emp_bound)
            apply (rule id_on_empty)
           apply (rule singl_bound[of "x"])
          apply (rule iffD2[OF disjoint_single])
          apply (rule provided)
             apply assumption+
      apply (rule terms_pre.UNION_bound)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
          apply (rule terms.var_large)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
      apply (rule terms.var_large)
        apply (erule conjE allE)+
        apply (erule impE)
         prefer 2
         apply (rule iffD2[OF arg_cong2[of _ _ _ _ fresh]])
          apply (rule sym)
           apply assumption
          prefer 2
          apply (drule provided(2)[rotated -1])
            apply (rotate_tac -6)
            apply assumption+
         apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
          apply (rule not_in_imsupp_same[symmetric])
      apply (drule trans[OF Int_commute])
          apply (unfold disjoint_iff)[1]
          apply (erule allE)
          apply (erule impE)
           apply (rule UN_I)
            apply assumption+
      apply (rule id_apply[symmetric])

         apply (rule conjI)
          apply (rule UnI2)
         apply (rule singletonI)
        apply assumption

       apply (rule iffD2[OF arg_cong3[OF _ refl refl, of _ _ Ty]])
        apply (rule arg_cong3[OF refl _ refl, of _ _ extend])
        apply (rule not_in_imsupp_same[symmetric])
        apply assumption
      unfolding provided(3)[symmetric]
       apply (rule iffD1[OF rename_Ty])
      apply assumption+


       apply (unfold Abs_inject)[1]
       apply (erule exE conjE)+
       apply hypsubst
       apply (unfold terms_vvsubst_rrename[symmetric])[1]
       apply (rule exE[OF ex_avoiding_bij])
               apply (rotate_tac -3)
               apply assumption
              apply assumption
             apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
            prefer 2
            apply assumption
           apply (rule terms.card_of_FFVars_bounds)
          apply (rule singl_bound[of "x"])
         apply (rule iffD2[OF disjoint_single])
         apply (rule provided)
            apply assumption+
        apply (rule terms_pre.UNION_bound)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
          apply (rule terms.var_large)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
        apply (rule terms.var_large)
       apply (erule conjE)+
       apply (rotate_tac -2)
      apply (erule allE)
       apply (rule iffD2[OF arg_cong3[OF _ _ refl, of _ _ _ _ Ty]])
         apply (rule arg_cong3[OF refl _ refl, of _ _ extend])
         apply (rule sym)
         apply (erule impE)
          apply (rule conjI)
           apply (rule UnI2)
           apply (rule singletonI)
          apply assumption
         apply assumption
        apply (rule terms.map_cong0)
          apply assumption
         apply (rotate_tac -4)
      apply assumption
        apply (unfold FFVars_terms_simps)[1]
      subgoal for y e' f' g z
        apply (rule case_split[of "z \<in> {x}"])
          apply (drule singletonD)
         apply hypsubst_thin
         apply (erule impE)
          apply (rule conjI)
           apply (rule UnI2)
           apply (rule singletonI)
          apply assumption
         apply (rule sym)
         apply assumption
        apply (drule id_onD)
         apply (rule DiffI)
          apply assumption
         apply assumption
        apply (drule id_onD)
         apply (rule DiffI)
          apply assumption
         apply assumption
        apply (rule trans)
         apply assumption
        apply (rule sym)
        apply assumption
        done
      subgoal for y e' f' g
       apply (rule iffD2[OF arg_cong3[OF _ refl refl, of _ _ Ty]])
      apply (rule trans)
        apply (rule arg_cong3[OF _ refl refl, of _ _ extend])
          prefer 2
          apply (rule provided(3)[symmetric, of "g"])
        apply assumption+
      apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
          apply (drule trans[OF Int_commute])
          apply (unfold disjoint_iff)[1]
          apply (erule allE)+
          apply (rotate_tac -1)
          apply (erule impE)
           apply (rule UN_I)
            apply assumption
           apply assumption
          apply (rule not_in_imsupp_same[symmetric])
          apply assumption
         apply (rule id_apply[symmetric])
        apply (rule iffD1[OF rename_Ty])
          apply assumption+
        done
      apply (rule allI)
      apply (rule iffD2[OF fun_cong[of "P _ _ _"]])
       apply (rule arg_cong3[OF _ refl refl])
       apply (rule arg_cong3[OF refl _ refl, of _ _ extend])
       apply (rule not_in_imsupp_same[symmetric])
       apply assumption
      unfolding provided(3)[symmetric]
      apply (rule clD[of P, rotated])
        apply assumption+
      apply (unfold Abs_inject)
      apply (erule exE conjE)+
      apply hypsubst_thin
      apply (unfold terms_vvsubst_rrename[symmetric])
      apply (rule exE[OF ex_avoiding_bij])
              apply (rotate_tac -3)
              apply assumption
      apply assumption
            apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
           prefer 2
           apply assumption
          apply (rule terms.card_of_FFVars_bounds)
         apply (rule singl_bound)
        apply (rule iffD2[OF disjoint_single])
      apply (rule provided)
        apply assumption+
      apply (rule terms_pre.UNION_bound)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
          apply (rule terms.var_large)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
       apply (rule terms.var_large)
      apply (erule conjE)+
      apply (rotate_tac -2)
      apply (erule allE)
      apply (rule iffD2[OF fun_cong[of "cl _ _ _ _"]])
       apply (rule fun_cong[of "cl _ _ _"])
       apply (rule arg_cong3[OF refl _ _, of _ _ _ _ cl])
        apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ extend])
      defer
        apply (erule impE)
         prefer 2
         apply (rule sym)
         apply assumption
        apply (rule conjI)
         apply (rule UnI2)
         apply (rule singletonI)
        apply assumption
       apply (rule terms.map_cong0)
         apply assumption
        apply (rotate_tac -4)
      apply assumption+
      subgoal for y e' \<rho> f' g z
        apply (rule case_split[of "z \<in> {x}"])
         apply (drule singletonD)
         apply hypsubst_thin
         apply (erule impE)
          apply (rule conjI)
           apply (rule UnI2)
           apply (rule singletonI)
          apply assumption
         apply (rule sym)
         apply assumption
        unfolding FFVars_terms_simps
        apply (drule id_onD, rule DiffI, assumption+)+
        apply (rule trans)
         apply assumption
        apply (rule sym)
        apply assumption
        done
       apply (rule iffD2[OF fun_cong[of "cl _ _ _ _"]])
        apply (rule fun_cong[of "cl _ _ _"])
        apply (rule arg_cong3[OF refl _ refl, of _ _ cl])
        apply (rule provided(3)[symmetric, of _ x])
         apply assumption+
       apply (rule cl_vvsubst)
         apply assumption+
       apply (erule allE)
       apply assumption
  apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
          apply (drule trans[OF Int_commute])
       apply (unfold disjoint_iff)[1]
       apply (rule not_in_imsupp_same[symmetric])
       apply (erule allE)+
       apply (rotate_tac -1)
       apply (erule impE)
        apply (rule UN_I)
         apply assumption+
      apply (rule id_apply[symmetric])
      done
  done
  done

lemma Ty_fresh_induct:
  fixes A::"'a::var_terms_pre set" and e::"'a terms"
  assumes "|A| <o |UNIV::'a set|" and x: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>"
    and Ty_Var: "\<And>x \<tau> \<Gamma>. (x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> P \<Gamma> (Var x) \<tau>"
    and Ty_App: "\<And>\<Gamma> e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2. \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 \<Longrightarrow> P \<Gamma> e1 (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1 \<Longrightarrow> P \<Gamma> e2 \<tau>\<^sub>1 \<Longrightarrow> P \<Gamma> (App e1 e2) \<tau>\<^sub>2"
    and Ty_Abs: "\<And>x \<Gamma> \<tau> e \<tau>\<^sub>2. x \<notin> A \<union> fst ` fset \<Gamma> \<union> FFVars_terms (Abs x \<tau> e) \<Longrightarrow> x \<sharp> \<Gamma> \<Longrightarrow> \<Gamma>,x:\<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<Longrightarrow> P (\<Gamma>,x:\<tau>) e \<tau>\<^sub>2 \<Longrightarrow> P \<Gamma> (Abs x \<tau> e) (\<tau> \<rightarrow> \<tau>\<^sub>2)"
  shows "P \<Gamma> e \<tau>"
  apply (rule mp[OF spec[OF Ty_fresh_induct_param[of _ _ _ "\<lambda>\<rho>. case \<rho> of (\<Gamma>, e) \<Rightarrow> A \<union> fst ` fset \<Gamma> \<union> FFVars_terms e" "\<lambda>\<Gamma> e \<tau> \<rho>. \<rho> = (\<Gamma>, e) \<longrightarrow> P \<Gamma> e \<tau>"]]])
  apply (rule assms)+
       apply (rule allI)
  subgoal for x
    apply (rule prod.exhaust[of x])
    apply hypsubst_thin
    unfolding prod.case
    apply (rule terms.Un_bound)
     apply (rule terms.Un_bound)
    apply (rule assms(1))
     apply (rule ordLeq_ordLess_trans[OF card_of_image])
     apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))) 1\<close>)
     apply (rule terms_pre.var_large)
    apply (rule terms.set_bd_UNIV)
    done
     apply (rule impI)
     apply (rule Ty_Var)
     apply assumption
    apply (rule impI)
  apply (erule allE, erule impE, rule refl)+
    apply (rule Ty_App)
       apply assumption+
   apply (rule impI)
   apply (rule Ty_Abs)
  subgoal for x \<Gamma> \<tau> e \<tau>2 y
    apply (rule prod.exhaust[of y])
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    unfolding prod.case Un_iff de_Morgan_disj
    apply (erule conjE)+
    apply (rule conjI)+
     apply assumption+
    done
     apply assumption+
   apply (erule allE)
   apply (erule impE)
    apply (rule refl)
   apply assumption
  apply (rule refl)
  done

lemmas Ty_induct_strong = Ty_fresh_induct[OF emp_bound, unfolded Un_empty_left]

inductive_cases
  Ty_VarE[elim]: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Var x : \<tau>"
  and Ty_AppE[elim]: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y App e1 e2 : \<tau>\<^sub>2"
print_theorems

lemma provided_strong:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a" and \<Gamma>::"('a \<times> \<tau>) fset"
  shows "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> x \<sharp> \<Gamma> \<longleftrightarrow> f x \<sharp> map_prod f id |`| \<Gamma>"
  apply (rule iffI)
   apply (rule provided)
  apply assumption+
  apply (drule provided[rotated -1])
    apply (rule bij_imp_bij_inv)
  apply assumption
  apply (rule supp_inv_bound)
  apply assumption+
  unfolding inv_simp1 fset.map_comp comp_def prod.map_comp id_def
  unfolding id_def[symmetric] prod.map_id fset.map_id
  apply assumption
  done

(* automate with binder_inductive_cases *)
lemma Ty_AbsE:
  fixes e::"'a::var_terms_pre terms" and A::"'a set"
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau>\<^sub>1 e : \<tau>" "|A| <o |UNIV::'a set|"
    and "\<And>y e' \<tau>' \<tau>\<^sub>2. y \<notin> A \<Longrightarrow> Abs x \<tau>\<^sub>1 e = Abs y \<tau>' e' \<Longrightarrow> \<tau> = (\<tau>' \<rightarrow> \<tau>\<^sub>2) \<Longrightarrow> y \<sharp> \<Gamma> \<Longrightarrow> \<Gamma>,y:\<tau>' \<turnstile>\<^sub>t\<^sub>y e' : \<tau>\<^sub>2 \<Longrightarrow> P"
  shows P
  apply (rule mp[OF Ty_fresh_induct[OF assms(2,1), of "\<lambda>\<Gamma>' e' \<tau>'. \<Gamma>' = \<Gamma> \<and> e' = Abs x \<tau>\<^sub>1 e \<and> \<tau>' = \<tau> \<longrightarrow> P"]])
     apply (rule impI, (erule conjE)+, rotate_tac -2, erule notE[rotated], rule terms_distinct)+
   apply (rule impI)
   apply (erule conjE)+
   apply hypsubst
  unfolding Un_iff de_Morgan_disj
   apply (erule conjE)+
   apply (rule assms(3))
       apply assumption
      apply (rule sym)
      apply assumption+
  apply (rule conjI refl)+
  done
lemma Ty_AbsE':
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau>\<^sub>1 e : \<tau>" "x \<notin> \<Union>(Basic_BNFs.fsts ` fset \<Gamma>)"
and "\<And>\<tau>\<^sub>2. \<tau> = (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2) \<Longrightarrow> x \<sharp> \<Gamma> \<Longrightarrow> \<Gamma>,x:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<Longrightarrow> P"
shows "P"
  apply (rule Ty_AbsE)
    apply (rule assms(1))
  apply (rule terms_pre.UNION_bound)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
          apply (rule terms.var_large)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
   apply (rule terms.var_large)

  unfolding Abs_inject
  apply (erule exE conjE)+
  apply hypsubst

  apply (rule exE[OF ex_avoiding_bij])
          apply assumption+
        apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
       apply (rule terms.set_bd_UNIV)
      apply assumption
     apply (rule singl_bound)
    apply (rule iffD2[OF disjoint_single])
  apply (rule assms(2))
apply (rule terms_pre.UNION_bound)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
          apply (rule terms.var_large)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
   apply (rule terms.var_large)
  apply (erule conjE)+

  apply (rule assms(3))
    apply assumption
   apply (drule iffD1[OF arg_cong2[of _ _ _ _ "\<lambda>a b. a \<sharp> b"], rotated -1])
     apply (erule allE)
     apply (erule impE)
      prefer 2
      apply (rule sym)
      apply assumption
     apply (rule conjI)
      apply (rule UnI2)
      apply (rule singletonI)
     apply assumption
    prefer 2
    apply (rule iffD2[OF provided_strong])
      apply (rotate_tac -6)
      apply assumption+
 apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
  apply (drule trans[OF Int_commute])
       apply (unfold disjoint_iff)[1]
    apply (rule not_in_imsupp_same[symmetric])
    apply (erule allE)+
    apply (rotate_tac -1)
    apply (erule impE)
     apply (rule UN_I)
      apply assumption+
   apply (rule id_apply[symmetric])

  apply (rule iffD2[OF rename_Ty])
    apply (rotate_tac -5)
    apply assumption+
  unfolding provided
  apply (rule iffD2[OF arg_cong3[OF _ _ refl, of _ _ _ _ Ty], rotated -1])
    apply assumption
   apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ extend])
  apply (rule sym)
apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
  apply (drule trans[OF Int_commute])
       apply (unfold disjoint_iff)[1]
     apply (rule not_in_imsupp_same[symmetric])
     apply (rotate_tac -1)
     apply (erule allE)
     apply (erule impE)
      apply (rule UN_I)
       apply assumption+
    apply (rule id_apply[symmetric])
   apply (erule allE)
   apply (erule impE)
    prefer 2
    apply assumption
   apply (rule conjI)
    apply (rule UnI2)
    apply (rule singletonI)
   apply assumption
  apply (rule trans[rotated])
   apply (rule fun_cong[OF terms_vvsubst_rrename])
    apply assumption+
  apply (rule terms.map_cong0)
    apply assumption+
  subgoal for y e' \<tau>' \<tau>2 f g z
    apply (rule case_split[of "z \<in> {x}"])
     apply (drule singletonD)
     apply hypsubst
     apply (erule allE)
     apply (erule impE)
      prefer 2
      apply assumption
     apply (rule conjI)
      apply (rule UnI2)
      apply (rule singletonI)
     apply assumption
    unfolding FFVars_terms_simps
    apply (drule id_onD, rule DiffI, assumption+)+
    apply (rule trans)
     apply assumption
    apply (rule sym)
    apply assumption
    done
  done

context begin
ML_file \<open>Tools/binder_induction.ML\<close>
end

lemma context_invariance: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>' \<Longrightarrow> \<forall>x\<in>FFVars_terms e. \<forall>\<tau>. (x, \<tau>) |\<in>| \<Gamma> \<longrightarrow> (x, \<tau>) |\<in>| \<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>t\<^sub>y e : \<tau>'"
proof (binder_induction \<Gamma> e \<tau>' arbitrary: \<Gamma>' avoiding: \<Gamma>' rule: Ty_fresh_induct_param)
  case (Ty_Var x \<tau> \<Gamma> \<Gamma>')
  then show ?case by (auto intro: Ty.Ty_Var)
next
  case (Ty_App \<Gamma> e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2 \<Gamma>')
  then show ?case unfolding FFVars_terms_simps by (meson Ty.Ty_App UnI1 UnI2)
next
  case (Ty_Abs x \<Gamma> \<tau> e \<tau>\<^sub>2 \<Gamma>')
  then have "\<forall>y\<in>FFVars_terms e. \<forall>\<tau>'. (y, \<tau>') |\<in>| \<Gamma>,x:\<tau> \<longrightarrow> (y, \<tau>') |\<in>| \<Gamma>',x:\<tau>"
    by (metis DiffI FFVars_terms_simps(3) fimageI finsert_iff fresh_def fst_conv fsts.cases prod_set_simps(1))
  moreover have "x \<sharp> \<Gamma>'" using Ty_Abs unfolding fresh_def
    by (metis UN_I fimageE fmember.rep_eq fsts.intros)
  ultimately show ?case using Ty_Abs by (auto intro: Ty.Ty_Abs)
qed

lemma substitution: "\<lbrakk> \<Gamma>,x:\<tau>' \<turnstile>\<^sub>t\<^sub>y e : \<tau> ; x \<sharp> \<Gamma> ; {||} \<turnstile>\<^sub>t\<^sub>y v : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x:=v)) e : \<tau>"
proof (binder_induction e arbitrary: \<Gamma> \<tau> avoiding: \<Gamma> x v rule: TT_fresh_induct_param)
  case (Var a \<Gamma> \<tau>)
  then have 2: "(a, \<tau>) |\<in>| \<Gamma>,x:\<tau>'" by blast
  from \<open>{||} \<turnstile>\<^sub>t\<^sub>y v : \<tau>'\<close> have 3: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y v : \<tau>'" using context_invariance by blast
  then show ?case unfolding tvsubst_simps[OF SSupp_upd_VVr_bound] unfolding fun_upd_def
  proof (cases "a = x")
    case True
    then have "\<tau> = \<tau>'" using 2 Var(1) unfolding fresh_def
      by (metis Var(2) Pair_inject finsertE fresh_def fst_eqD rev_fimage_eqI)
    then show "\<Gamma> \<turnstile>\<^sub>t\<^sub>y if a = x then v else VVr a : \<tau>" using True 3 by simp
  next
    case False
    then have "(a, \<tau>) |\<in>| \<Gamma>" using 2 by blast
    then show "\<Gamma> \<turnstile>\<^sub>t\<^sub>y if a = x then v else VVr a : \<tau>" unfolding VVr_eq_Var using False Ty.Ty_Var by auto
  qed
next
  case (App e1 e2 \<Gamma> \<tau>)
  from App(3) obtain \<tau>\<^sub>1 where "\<Gamma>,x:\<tau>' \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>" "\<Gamma>,x:\<tau>' \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1" by blast
  then have "\<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := v)) e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := v)) e2 : \<tau>\<^sub>1" using App by blast+
  then have "\<Gamma> \<turnstile>\<^sub>t\<^sub>y App (tvsubst (VVr(x := v)) e1) (tvsubst (VVr(x := v)) e2) : \<tau>" using Ty_App by blast
  then show ?case unfolding tvsubst_simps(2)[OF SSupp_upd_VVr_bound, symmetric] .
next
  case (Abs y \<tau>\<^sub>1 e \<Gamma> \<tau>)
  then have 1: "y \<notin> IImsupp (VVr(x:=v))" by (simp add: IImsupp_def SSupp_def)
  have "y \<notin> \<Union>(Basic_BNFs.fsts ` fset (\<Gamma>,x:\<tau>'))" using Abs(1) unfolding fresh_def by auto
  then obtain \<tau>\<^sub>2 where 2: "(\<Gamma>,x:\<tau>'),y:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2" "\<tau> = (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2)" using Abs(3) Ty_AbsE' by metis
  moreover have "(\<Gamma>,x:\<tau>'),y:\<tau>\<^sub>1 = (\<Gamma>,y:\<tau>\<^sub>1),x:\<tau>'" by blast
  moreover have "x \<sharp> \<Gamma>,y:\<tau>\<^sub>1" using Abs(1,4) unfolding fresh_def by auto
  ultimately have "\<Gamma>,y:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := v)) e : \<tau>\<^sub>2" using Abs(2,5) by metis
  moreover have "y \<sharp> \<Gamma>" using Abs(1) unfolding fresh_def
    by (metis UN_I UnI1 fimageE fmember.rep_eq fsts.intros)
  ultimately show ?case unfolding tvsubst_simps(3)[OF SSupp_upd_VVr_bound 1] using Ty_Abs 2(2) by blast
qed

theorem progress: "{||} \<turnstile>\<^sub>t\<^sub>y e : \<tau> \<Longrightarrow> (\<exists>x \<tau> e'. e = Abs x \<tau> e') \<or> (\<exists>e'. e \<longrightarrow> e')"
proof (induction "{||} :: ('a::var_terms_pre * \<tau>) fset" e \<tau> rule: Ty.induct)
  case (Ty_App e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2)
  from Ty_App(2) show ?case using ST_Beta ST_App by blast
qed auto

theorem preservation: "\<lbrakk> {||} \<turnstile>\<^sub>t\<^sub>y e : \<tau> ; e \<longrightarrow> e' \<rbrakk> \<Longrightarrow> {||} \<turnstile>\<^sub>t\<^sub>y e' : \<tau>"
proof (induction "{||} :: ('a::var_terms_pre * \<tau>) fset" e \<tau> arbitrary: e' rule: Ty.induct)
  case (Ty_App e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2)
  from Ty_App(5) show ?case
  proof cases
    case (ST_Beta x \<tau> e e2')
    then have "{||} \<turnstile>\<^sub>t\<^sub>y App (Abs x \<tau> e) e2 : \<tau>\<^sub>2" using Ty_App Ty.Ty_App by fastforce
    have "{||} \<turnstile>\<^sub>t\<^sub>y Abs x \<tau>\<^sub>1 e : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2" using Ty_App ST_Beta
      by (smt (verit, ccfv_SIG) Abs_inject App_inject Ty.cases \<tau>.inject terms_distinct(2) terms_distinct(4))
    then have "{||},x:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2" by (auto elim: Ty_AbsE')
    then have "{||} \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := e2')) e : \<tau>\<^sub>2" using substitution ST_Beta(1) Ty_App(3) unfolding fresh_def by fastforce
    then show ?thesis using ST_Beta by simp
  next
    case (ST_App e e1' e2')
    then have "{||} \<turnstile>\<^sub>t\<^sub>y e1' : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2" using Ty_App by simp
    then show ?thesis using Ty_App Ty.Ty_App ST_App by fastforce
  qed
next
  case (Ty_Abs x \<tau> e \<tau>\<^sub>2)
  from \<open>Abs x \<tau> e \<longrightarrow> e'\<close> show ?case by cases auto
qed auto

end