theory Composition
  imports "thys/MRBNF_Recursor"
begin

declare [[mrbnf_internals]]

datatype \<kappa> =
  Star ("\<star>")
  | KArrow \<kappa> \<kappa> (infixr "\<rightarrow>" 50)

(*
binder_datatype 'var \<tau> =
  | TyVar 'var
  | TyArrow
  | TyApp "'var \<tau>" "'var \<tau>"
  | TyForall a::"'var" \<kappa> t::"'var \<tau>" binds a in t

  \<down>

  'tyvar
+ unit
+ 'rec * 'rec
+ 'btyvar * \<kappa> * 'body
*)

declare [[ML_print_depth=10000000]]
local_setup \<open>fn lthy =>
let
  val systemf_type_name = "\<tau>_pre"
  val systemf_type = @{typ "'tyvar + unit + 'rec * 'rec + 'btyvar * \<kappa> * 'body"}
  val Xs = []
  val resBs = map dest_TFree [@{typ 'tyvar}, @{typ 'btyvar}, @{typ 'body}, @{typ 'rec}]
  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (systemf_type_name ^ "_")

  val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ false MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var)] systemf_type
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val ((mrbnf, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name systemf_type_name) true (fst tys) [] mrbnf lthy
  val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy
  val (_, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [(("\<tau>", mrbnf), 2)] [[0]] lthy
in lthy end
\<close>
print_theorems
print_bnfs
print_mrbnfs

ML \<open>
val tau = the (MRBNF_Def.mrbnf_of @{context} "Composition.\<tau>_pre")
\<close>

lemma infinite_var_\<tau>_pre: "infinite (UNIV :: 'a::var_\<tau>_pre set)"
  by (rule cinfinite_imp_infinite[OF \<tau>_pre.UNIV_cinfinite])

(******************** Definitions for variable-for-variable substitution ***********)
typedef 'a :: var_\<tau>_pre ssfun = "{f :: 'a \<Rightarrow> 'a. |supp f| <o |UNIV::'a set|}"
  apply (rule exI[of _ id])
  apply (rule iffD2[OF mem_Collect_eq])
  apply (rule supp_id_bound)
  done

definition idSS where "idSS \<equiv> Abs_ssfun id"
lemma idSS_rep_eq: "Rep_ssfun idSS = id"
  unfolding idSS_def
  apply (rule Abs_ssfun_inverse)
  apply (rule iffD2[OF mem_Collect_eq])
  apply (rule supp_id_bound)
  done

definition compSS where "compSS u p \<equiv> Abs_ssfun (u \<circ> Rep_ssfun p \<circ> inv u)"

lemma compSS_rep_eq: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> Rep_ssfun (compSS u x) = u \<circ> Rep_ssfun x \<circ> inv u"
  unfolding compSS_def
  apply (rule Abs_ssfun_inverse)
  apply (rule iffD2[OF mem_Collect_eq])
  apply (rule supp_comp_bound)
    apply (rule supp_inv_bound)
     apply assumption+
   apply (rule supp_comp_bound)
     apply (rule iffD1[OF mem_Collect_eq Rep_ssfun])
    apply assumption
   apply (rule infinite_var_\<tau>_pre)+
  done

lemma compSS_id: "compSS id = id"
  unfolding compSS_def comp_def id_def inv_id[unfolded id_def] Rep_ssfun_inverse
  apply (rule refl)
  done

lemma compSS_comp:
  fixes f g::"'a::var_\<tau>_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "compSS (f \<circ> g) = compSS f \<circ> compSS g"
  unfolding compSS_def comp_def
  apply (rule ext)
  apply (rule arg_cong[of _ _ Abs_ssfun])
  apply (rule ext)
  apply (rule arg_cong[of _ _ f])
  apply (rule sym)
  apply (rule trans)
   apply (rule fun_cong[of _ _ "inv _ _"])
   apply (rule Abs_ssfun_inverse)
   apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]])
  apply (rule trans)
     apply (rule comp_def[symmetric, of g])
    apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
    apply (rule comp_def[symmetric, of "Rep_ssfun _"])
  unfolding comp_assoc[symmetric]
   apply (rule iffD2[OF mem_Collect_eq])
   apply (rule supp_comp_bound)
     apply (rule supp_inv_bound)
      apply (rule assms)+
    apply (rule supp_comp_bound)
      apply (rule iffD1[OF mem_Collect_eq Rep_ssfun])
     apply (rule assms infinite_var_\<tau>_pre)+
  apply (rule arg_cong[of _ _ "\<lambda>x. g (Rep_ssfun _ x)"])
  apply (rule trans)
   apply (rule comp_apply[symmetric, of "inv g" "inv f"])
  apply (rule fun_cong[of "_ \<circ> _"])
  apply (rule trans)
   apply (rule o_inv_distrib[symmetric])
    apply (rule assms)+
  unfolding comp_def
  apply (rule refl)
  done

definition PFVars where "PFVars \<equiv> \<lambda>p. imsupp (Rep_ssfun p)"

lemma compSS_cong_id:
  fixes f::"'a::var_\<tau>_pre \<Rightarrow> 'a" and d::"'a ssfun"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "(\<And>a. a \<in> PFVars d \<Longrightarrow> f a = a) \<Longrightarrow> compSS f d = d"
  unfolding compSS_def PFVars_def comp_def
  apply (rule trans)
   apply (rule arg_cong[of _ _ Abs_ssfun])
   apply (rule ext)
   apply (rule imsupp_commute[of f "Rep_ssfun d", unfolded fun_eq_iff o_apply, rule_format])
   apply (rule bij_imsupp_supp_ne[OF assms(1)])
  apply (rule trans[OF Int_commute])
   apply (rule iffD2[OF disjoint_iff])
   apply (rule allI)
   apply (rule impI)
   apply (rule iffD2[OF not_in_supp_alt])
   apply assumption
  unfolding inv_simp2[OF assms(1)]
  apply (rule Rep_ssfun_inverse)
  done

lemma small_PFVars: "|PFVars (p::'a::var_\<tau>_pre ssfun)| <o |UNIV::'a set|"
  unfolding PFVars_def
  apply (rule iffD2[OF imsupp_supp_bound])
   apply (rule infinite_var_\<tau>_pre)
  apply (rule iffD1[OF mem_Collect_eq Rep_ssfun])
  done

lemma PFVars_Pmap:
  fixes f::"'a::var_\<tau>_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "PFVars (compSS f d) = f ` PFVars d"
  unfolding PFVars_def compSS_def comp_def
  apply (rule trans)
   apply (rule arg_cong[of _ _ imsupp])
   apply (rule Abs_ssfun_inverse)
  apply (rule iffD2[OF mem_Collect_eq])
   apply (rule supp_comp_bound[OF supp_inv_bound[OF assms] supp_comp_bound[OF iffD1[OF mem_Collect_eq Rep_ssfun] assms(2) infinite_var_\<tau>_pre] infinite_var_\<tau>_pre, unfolded comp_def])
  apply (rule imsupp_comp_image[unfolded comp_def, OF assms(1)])
  done

definition CCTOR :: "('a::var_\<tau>_pre, 'a, 'a \<tau> \<times> ('a ssfun \<Rightarrow> 'a \<tau>), 'a \<tau> \<times> ('a ssfun \<Rightarrow> 'a \<tau>)) \<tau>_pre \<Rightarrow> 'a ssfun \<Rightarrow> 'a \<tau>" where
  "CCTOR = (\<lambda>x p. \<tau>_ctor (map_\<tau>_pre (Rep_ssfun p) id ((\<lambda>R. R p) o snd) ((\<lambda>R. R p) o snd) x))"

lemma UFVars_subset: "set2_\<tau>_pre y \<inter> (PFVars p \<union> {}) = {} \<Longrightarrow>
       (\<And>t pu p. (t, pu) \<in> set3_\<tau>_pre y \<union> set4_\<tau>_pre y \<Longrightarrow> FFVars_\<tau> (pu p) \<subseteq> FFVars_\<tau> t \<union> PFVars p \<union> {}) \<Longrightarrow>
       FFVars_\<tau> (CCTOR y p) \<subseteq> FFVars_\<tau> (\<tau>_ctor (map_\<tau>_pre id id fst fst y)) \<union> PFVars p \<union> {}"
  unfolding Un_empty_right CCTOR_def PFVars_def
  apply (auto simp: imsupp_supp_bound[OF infinite_var_\<tau>_pre] \<tau>.FFVars_cctors \<tau>_pre.set_map supp_id_bound emp_bound Rep_ssfun[simplified])
  using imsupp_def supp_def apply fastforce
  using imsupp_def supp_def apply fastforce
  by fastforce+

lemma Umap_Uctor: "bij (f::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow>
       |supp f| <o |UNIV::'a set| \<Longrightarrow>
       rrename_\<tau> f (CCTOR y p) =
       CCTOR (map_\<tau>_pre f f (\<lambda>(t, pu). (rrename_\<tau> f t, \<lambda>p. rrename_\<tau> f (pu (compSS (inv f) p)))) (\<lambda>(t, pu). (rrename_\<tau> f t, \<lambda>p. rrename_\<tau> f (pu (compSS (inv f) p)))) y) (compSS f p)"
  unfolding CCTOR_def
  by (auto simp: \<tau>.rrename_id0s \<tau>.rrename_cctors \<tau>_pre.map_comp compSS_rep_eq Rep_ssfun[simplified]
      supp_comp_bound infinite_var_\<tau>_pre supp_inv_bound supp_id_bound inv_o_simp1[THEN rewriteR_comp_comp]
      fun_cong[OF compSS_comp[unfolded comp_def], symmetric] compSS_id[unfolded id_def]
      intro!: \<tau>.cctor_eq_intro_rrenames[of id] \<tau>_pre.map_cong)

(***************************************************************************************)

ML_file \<open>./Tools/mrbnf_recursor_tactics.ML\<close>
ML_file \<open>./Tools/mrbnf_recursor.ML\<close>

local_setup \<open>fn lthy =>
let
  fun rtac ctxt = resolve_tac ctxt o single
  val model_tacs = {
    small_avoiding_sets = [fn ctxt => rtac ctxt @{thm emp_bound} 1],
    Umap_id0 = fn ctxt => resolve_tac ctxt @{thms \<tau>.rrename_id0s} 1,
    Umap_comp0 = fn ctxt => EVERY1 [rtac ctxt @{thm \<tau>.rrename_comp0s[symmetric]}, REPEAT_DETERM o assume_tac ctxt],
    Umap_cong_ids = map (fn thm => fn ctxt => EVERY1 [
      resolve_tac ctxt [thm],
      REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
    ]) @{thms \<tau>.rrename_cong_ids},
    UFVars_Umap = [fn ctxt => EVERY1 [rtac ctxt @{thm \<tau>.FFVars_rrenames}, REPEAT_DETERM o assume_tac ctxt]],
    Umap_Uctor = fn ctxt => EVERY1 [rtac ctxt @{thm Umap_Uctor}, REPEAT_DETERM o assume_tac ctxt],
    UFVars_subsets = [fn ctxt => EVERY1 [
      rtac ctxt @{thm UFVars_subset},
      REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
    ]]
  };
  val parameter_tacs = {
    Pmap_id0 = fn ctxt => rtac ctxt @{thm compSS_id} 1,
    Pmap_comp0 = fn ctxt => EVERY1 [rtac ctxt @{thm compSS_comp}, REPEAT_DETERM o assume_tac ctxt],
    Pmap_cong_ids = [fn ctxt => EVERY1 [
      rtac ctxt @{thm compSS_cong_id},
      REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
    ]],
    PFVars_Pmap = [fn ctxt => EVERY1 [rtac ctxt @{thm PFVars_Pmap}, REPEAT_DETERM o assume_tac ctxt]],
    small_PFVars = [fn ctxt => rtac ctxt @{thm small_PFVars} 1]
  };
  val model = {
    U = @{typ "'a::var_\<tau>_pre \<tau>"},
    fp_result = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Composition.\<tau>"),
    UFVars = [@{term "\<lambda>(_::'a::var_\<tau>_pre \<tau>) (x::'a::var_\<tau>_pre \<tau>). FFVars_\<tau> x"}],
    Umap = @{term "\<lambda>f (_::'a::var_\<tau>_pre \<tau>) (x::'a::var_\<tau>_pre \<tau>). rrename_\<tau> f x"},
    Uctor = @{term CCTOR},
    avoiding_sets = [@{term "{}::'a::var_\<tau>_pre set"}],
    binding_dispatcher = [[0]],
    parameters = {
      P = @{typ "'a::var_\<tau>_pre ssfun"},
      PFVars = [@{term "PFVars"}],
      Pmap = @{term "compSS:: ('a::var_\<tau>_pre \<Rightarrow> 'a) \<Rightarrow> _ \<Rightarrow> _"},
      axioms = parameter_tacs
    },
    axioms = model_tacs
  };
  val lthy' = MRBNF_Recursor.create_binding_recursor model @{binding ff0} lthy
in lthy' end
\<close>
print_theorems

(************************************************************************************)

lemmas id_prems = supp_id_bound bij_id supp_id_bound

definition vvsubst where "vvsubst f x \<equiv> ff0_ff0 x (Abs_ssfun f)"

lemma ssfun_rep_eq: "|supp (f::'a::var_\<tau>_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> Rep_ssfun (Abs_ssfun f) = f"
  apply (rule Abs_ssfun_inverse)
  apply (rule iffD2[OF mem_Collect_eq])
  apply assumption
  done

lemma vvsubst_cctor:
  assumes "|supp (f::'a::var_\<tau>_pre \<Rightarrow> 'a)| <o |UNIV::'a set|"
  shows "set2_\<tau>_pre x \<inter> imsupp f = {} \<Longrightarrow> nnoclash_ff0 x \<Longrightarrow>
  vvsubst f (\<tau>_ctor x) = \<tau>_ctor (map_\<tau>_pre f id (vvsubst f) (vvsubst f) x)"
  unfolding vvsubst_def
  apply (rule trans)
   apply (rule ff0_cctor)
  unfolding CCTOR_def \<tau>_pre.map_comp[OF id_prems assms(1) bij_id supp_id_bound] id_o o_id ssfun_rep_eq[OF assms(1)]
  unfolding comp_def snd_conv Un_empty_right PFVars_def ssfun_rep_eq[OF assms(1)]
    apply assumption+
  apply (rule refl)
  done

lemma FFVars_vvsubst_weak:
  assumes "|supp (f::'a::var_\<tau>_pre \<Rightarrow> 'a)| <o |UNIV::'a set|"
  shows "FFVars_\<tau> (vvsubst f t) \<subseteq> FFVars_\<tau> t \<union> imsupp f"
  unfolding vvsubst_def
  by (rule ff0_UFVars[of _ "Abs_ssfun f", unfolded Un_empty_right PFVars_def ssfun_rep_eq[OF assms(1)]])

lemma not_in_imsupp_same: "z \<notin> imsupp f \<Longrightarrow> f z = z"
  unfolding imsupp_def supp_def by blast

theorem vvsubst_rrename:
  fixes t::"'a::var_\<tau>_pre \<tau>"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "vvsubst f t = rrename_\<tau> f t"
  apply (rule \<tau>.TT_fresh_co_induct[OF iffD2[OF imsupp_supp_bound[OF infinite_var_\<tau>_pre] assms(2)], of _ t])
  apply (rule trans)
   apply (rule vvsubst_cctor)
     apply (rule assms)
    apply (rule iffD2[OF disjoint_iff])
    apply (rule allI)
    apply (rule impI)
  apply assumption
  unfolding nnoclash_ff0_def Int_Un_distrib Un_empty
   apply (rule conjI)
    apply (rule iffD2[OF disjoint_iff])
    apply (rule allI)
    apply (rule impI)
    apply assumption
  apply (rule iffD2[OF disjoint_iff])
    apply (rule allI)
   apply (rule impI)
   apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
   apply (rule iffD2[OF bex_simps(8)])
   apply (rule ballI)
   apply assumption
  apply (rule sym)
  apply (rule trans)
   apply (rule \<tau>.rrename_cctors)
    apply (rule assms)
   apply (rule assms)
  apply (rule sym)
  apply (rule iffD2[OF \<tau>.TT_injects0])
  apply (rule exI)
  apply (rule conjI, rule bij_id supp_id_bound id_on_id)+
  unfolding \<tau>.rrename_id0s \<tau>_pre.map_id
  apply (rule \<tau>_pre.map_cong)
            apply (rule bij_id supp_id_bound assms refl)+
    apply (rule trans[OF id_apply])
  apply (rule sym)
    apply (rule not_in_imsupp_same)
    apply assumption+
  done

lemma vvsubst_id0: "vvsubst id = id"
  apply (rule trans)
  apply (rule ext)
   apply (rule vvsubst_rrename)
    apply (rule bij_id supp_id_bound)+
  apply (rule \<tau>.rrename_id0s)
  done

ML \<open>
fun Int_empty_tac ctxt = EVERY' [
  resolve_tac ctxt @{thms iffD2[OF disjoint_iff]},
  resolve_tac ctxt [allI],
  resolve_tac ctxt [impI],
  TRY o Goal.assume_rule_tac ctxt
];

fun helper_tac ctxt = EVERY1 [
  Int_empty_tac ctxt,
  K (Ctr_Sugar_Tactics.unfold_thms_tac ctxt @{thms nnoclash_ff0_def Int_Un_distrib Un_empty}),
  resolve_tac ctxt [conjI],
  Int_empty_tac ctxt,
  Int_empty_tac ctxt,
  resolve_tac ctxt @{thms iffD2[OF arg_cong[OF UN_iff, of Not]]},
  resolve_tac ctxt @{thms iffD2[OF bex_simps(8)]},
  resolve_tac ctxt [ballI],
  Goal.assume_rule_tac ctxt
];
\<close>

lemma Diff_image_not_in_imsupp: "(\<And>x. x \<in> B \<Longrightarrow> x \<notin> imsupp f) \<Longrightarrow> f ` A - B = f ` (A - B)"
  unfolding supp_def imsupp_def by fastforce

lemma FFVars_vvsubst:
  fixes t::"'a::var_\<tau>_pre \<tau>"
  assumes "|supp f| <o |UNIV::'a set|"
  shows "FFVars_\<tau> (vvsubst f t) = f ` FFVars_\<tau> t"
  apply (rule \<tau>.TT_fresh_co_induct[of _ _ t])
   apply (rule iffD2[OF imsupp_supp_bound[OF infinite_var_\<tau>_pre] assms])
  apply (rule trans)
   apply (rule arg_cong[of _ _ FFVars_\<tau>])
   apply (rule vvsubst_cctor)
     apply (rule assms)
    apply (tactic \<open>helper_tac @{context}\<close>)
  apply (rule trans)
   apply (rule \<tau>.FFVars_cctors)
  unfolding \<tau>_pre.set_map[OF assms bij_id supp_id_bound] image_id image_comp comp_def[of FFVars_\<tau>]
  apply (rule trans)
    apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
    apply (rule arg_cong2[OF refl, of _ _ "(\<union>)"])
    apply (rule trans)
     apply (rule arg_cong2[OF _ refl, of _ _ minus])
     apply (rule rel_set_UN_D)
     apply (rule rel_set_mono_strong[OF _ iffD2[OF fun_cong[OF fun_cong[OF rel_set_eq]] refl]])
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply assumption
  unfolding image_UN[symmetric]
    apply (rule Diff_image_not_in_imsupp)
  apply assumption
    apply (rule rel_set_UN_D)
    apply (rule rel_set_mono_strong[OF _ iffD2[OF fun_cong[OF fun_cong[OF rel_set_eq]] refl]])
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply assumption
  unfolding image_UN[symmetric] image_Un[symmetric] \<tau>.FFVars_cctors[symmetric]
  apply (rule refl)
  done

lemma ball_not_eq_imsupp: "x \<in> B \<Longrightarrow> x \<notin> A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<notin> imsupp f) \<Longrightarrow> \<forall>xa\<in>A. x \<noteq> f xa"
  unfolding imsupp_def supp_def by fastforce

lemma vvsubst_comp:
  fixes f g:: "'a::var_\<tau>_pre \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|" "|supp g| <o |UNIV::'a set|"
  shows "vvsubst (g \<circ> f) t = (vvsubst g \<circ> vvsubst f) t"
  apply (rule \<tau>.TT_fresh_co_induct[of _ _ t])
   apply (rule \<tau>_pre.Un_bound)
    apply (rule iffD2[OF imsupp_supp_bound[OF infinite_var_\<tau>_pre] assms(2)])
   apply (rule iffD2[OF imsupp_supp_bound[OF infinite_var_\<tau>_pre] assms(1)])
  apply (rule trans)
   apply (rule vvsubst_cctor)
     apply (rule supp_comp_bound)
       apply (rule assms infinite_var_\<tau>_pre)+
    apply (rule Int_subset_empty2[rotated])
     apply (rule imsupp_o)
  apply (tactic \<open>helper_tac @{context}\<close>)
  apply (rule sym)
  apply (rule trans)
   apply (rule trans[OF comp_apply])
   apply (rule arg_cong[of _ _ "vvsubst g"])
   apply (rule vvsubst_cctor)
     apply (rule assms)
    apply (rule Int_subset_empty2[rotated])
     apply (rule Un_upper2)
    apply (tactic \<open>helper_tac @{context}\<close>)
  apply (rule trans)
   apply (rule vvsubst_cctor)
     apply (rule assms)
  unfolding \<tau>_pre.set_map[OF assms(1) bij_id supp_id_bound] image_id nnoclash_ff0_def
    apply (rule Int_subset_empty2[rotated])
     apply (rule Un_upper1)
    apply (tactic \<open>Int_empty_tac @{context} 1\<close>)
  unfolding image_comp comp_def[of FFVars_\<tau>] FFVars_vvsubst[OF assms(1)] image_UN[symmetric]
   apply (tactic \<open>Int_empty_tac @{context} 1\<close>)
  unfolding Un_iff de_Morgan_disj image_iff bex_simps(8)
   apply (rule conjI)
    apply (rule ball_not_eq_imsupp)
      apply assumption+
    apply (rule conjunct2)
    apply assumption
   apply (rule ball_not_eq_imsupp)
     apply assumption
  unfolding UN_iff bex_simps(8)
    apply (rule ballI)
    apply assumption
   apply (rule conjunct2)
   apply assumption
  unfolding \<tau>_pre.map_comp[OF assms(1) bij_id supp_id_bound assms(2) bij_id supp_id_bound] id_o
  apply (rule trans)
   apply (rule arg_cong[of _ _ \<tau>_ctor])
   apply (rule \<tau>_pre.map_cong[OF _ _ _ _ _ _ refl refl refl])
          apply (rule assms infinite_var_\<tau>_pre supp_comp_bound bij_id supp_id_bound)+
    apply (rule sym, assumption)+
  apply (rule refl)
  done

lemma vvsubst_cong:
  fixes t::"'a::var_\<tau>_pre \<tau>"
  assumes "|supp f| <o |UNIV::'a set|" "|supp g| <o |UNIV::'a set|" "(\<And>a. a \<in> FFVars_\<tau> t \<Longrightarrow> f a = g a)"
  shows "vvsubst f t = vvsubst g t"
  apply (rule \<tau>.TT_fresh_co_induct[of _ "\<lambda>t. (\<forall>a. a \<in> FFVars_\<tau> t \<longrightarrow> f a = g a) \<longrightarrow> vvsubst f t = vvsubst g t" t, THEN mp, unfolded atomize_all[symmetric] atomize_imp[symmetric]])
    apply (rule \<tau>_pre.Un_bound)
     apply (rule iffD2[OF imsupp_supp_bound[OF infinite_var_\<tau>_pre] assms(2)])
    apply (rule iffD2[OF imsupp_supp_bound[OF infinite_var_\<tau>_pre] assms(1)])
  subgoal premises prems for v
    apply (rule trans)
     apply (rule vvsubst_cctor)
       apply (rule assms)
      apply (rule Int_subset_empty2[rotated])
       apply (rule Un_upper2)
      apply (insert prems)
      apply (tactic \<open>helper_tac @{context}\<close>)
    apply (rule sym)
    apply (rule trans)
     apply (rule vvsubst_cctor)
       apply (rule assms)
      apply (rule Int_subset_empty2[rotated])
       apply (rule Un_upper1)
      apply (tactic \<open>helper_tac @{context}\<close>)
    apply (rule sym)
    apply (rule trans)
     apply (rule arg_cong[of _ _ \<tau>_ctor])
     apply (rule \<tau>_pre.map_cong0[rotated -4])
              apply (drule UnI1)
              apply (drule UnI1)
    unfolding \<tau>.FFVars_cctors
              apply assumption
             apply (rule refl)
            apply (rule prems(1))
             apply assumption
            apply (drule UN_I)
             apply assumption
    subgoal for z a
      apply (rule bool.exhaust[of "a \<in> set2_\<tau>_pre v", unfolded eq_True eq_False])
       apply (tactic \<open>SELECT_GOAL (Ctr_Sugar_Tactics.unfold_thms_tac @{context} @{thms Un_iff de_Morgan_disj}) 1\<close>)
       apply (rule trans)
        apply (rule not_in_imsupp_same[of a])
        apply (rule conjunct2)
        apply assumption
       apply (rule sym)
       apply (rule not_in_imsupp_same)
       apply (rule conjunct1)
       apply assumption
      apply (rotate_tac -2)
      apply (drule DiffI)
       apply assumption
      apply (rotate_tac -1)
      apply (drule UnI2)
      apply (rotate_tac -1)
      apply (drule UnI1)
      apply assumption
      done
           apply (rule prems(2))
            apply assumption
           apply (drule UN_I)
            apply assumption
           apply (rotate_tac -1)
           apply (drule UnI2)
           apply assumption
          apply (rule assms bij_id supp_id_bound)+
    apply (rule refl)
    done
  apply (rule assms)
  apply assumption
  done

lemma TT_inject:
  fixes t t'::"('a::var_\<tau>_pre, 'a, 'a \<tau>, 'a \<tau>) \<tau>_pre"
  shows "\<tau>_ctor t = \<tau>_ctor t' \<longleftrightarrow> (\<exists>f. bij f \<and> |supp f| <o |UNIV::'a set| \<and> id_on (\<Union>(FFVars_\<tau> ` set3_\<tau>_pre t) - set2_\<tau>_pre t) f \<and> map_\<tau>_pre id f (vvsubst f) id t = t')"
  unfolding \<tau>.TT_injects0 conj_assoc[symmetric]
  apply (rule ex_cong)
  apply (erule conjE)+
  unfolding vvsubst_rrename
  subgoal premises prems for f
    unfolding vvsubst_rrename[OF prems(2,3)]
    apply (rule refl)
    done
  done

end
