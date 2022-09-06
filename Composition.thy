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

  val ((mrbnf, tys), (accum, lthy')) = MRBNF_Comp.mrbnf_of_typ false MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var)] systemf_type
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val ((mrbnf, (Ds, info)), lthy'') = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name systemf_type_name) true (fst tys) [] mrbnf lthy'
  val (bnf, lthy''') = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy''
in lthy''' end
\<close>
print_theorems
print_bnfs
print_mrbnfs

ML \<open>
val tau = the (MRBNF_Def.mrbnf_of @{context} "Composition.\<tau>_pre")
\<close>

ML \<open>
Multithreading.parallel_proofs := 1;
\<close>

local_setup \<open>fn lthy =>
let
  val (_, lthy') = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP
    [(("\<tau>", tau), 2)] [[0]] lthy
in
  lthy'
end
\<close>
print_theorems

lemma infinite_var_\<tau>_pre: "infinite (UNIV :: 'a::var_\<tau>_pre set)"
  using card_of_ordLeq_finite cinfinite_def infinite_regular_card_order.Cinfinite infinite_regular_card_order_card_suc natLeq_Card_order natLeq_card_order natLeq_cinfinite var_DEADID_class.large by blast

lemma Un_bound:
  assumes inf: "infinite (UNIV :: 'a set)"
    and "|A1| <o |UNIV::'a set|" and "|A2| <o |UNIV::'a set|"
  shows "|A1 \<union> A2| <o |UNIV::'a set|"
  using assms card_of_Un_ordLess_infinite by blast

lemma imsupp_supp_bound: "infinite (UNIV::'a set) \<Longrightarrow> |imsupp g| <o |UNIV::'a set| \<longleftrightarrow> |supp g| <o |UNIV::'a set|"
  by (metis Un_bound card_of_image imsupp_def ordLeq_ordLess_trans supp_ordleq_imsupp)

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

ML \<open>
val unfold_thms_tac = Ctr_Sugar_Tactics.unfold_thms_tac
fun rtac ctxt = resolve_tac ctxt o single
fun etac ctxt = eresolve_tac ctxt o single
fun dtac ctxt = dresolve_tac ctxt o single

val var_types = MRBNF_Def.var_types_of_mrbnf tau
val rename_t = @{term "rename_\<tau> :: ('a::var_\<tau>_pre => 'a) \<Rightarrow> _ \<Rightarrow> _"}
val vars = [@{typ "'a::var_\<tau>_pre"}]
val raw_T = @{typ "'a::var_\<tau>_pre raw_\<tau>"}
val Pmap_t = @{term "Pmap_ff0 :: ('a::var_\<tau>_pre => 'a) \<Rightarrow> _ \<Rightarrow> _"}
val pre_T = MRBNF_Def.mk_T_of_mrbnf [] [raw_T, raw_T] vars vars tau
val ctor_t = @{term "raw_\<tau>_ctor :: _ \<Rightarrow> 'a::var_\<tau>_pre raw_\<tau>"}
val FVars_t = @{term "FVars_\<tau> :: _ \<Rightarrow> 'a::var_\<tau>_pre set"}
val PFVars_t = @{term "PFVars_ff0 :: _ \<Rightarrow> 'a::var_\<tau>_pre set"}

fun swapped thm a b = [thm OF [a, b], thm OF [b, a]]
fun mk_prems frees bounds = maps (fn MRBNF_Def.Free_Var => frees | MRBNF_Def.Bound_Var => bounds | _ => [])
\<close>

lemmas id_prems = supp_id_bound bij_id supp_id_bound

lemma Uctor_cong: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> bij (u'::'a \<Rightarrow> 'a) \<Longrightarrow> |supp u'| <o |UNIV::'a set| \<Longrightarrow>
  (\<And>t pd p. (t, pd) \<in> set3_\<tau>_pre x \<union> set4_\<tau>_pre x \<Longrightarrow> UFVars_ff0 t (pd p) \<subseteq> FFVars_\<tau> t \<union> PFVars_ff0 p \<union> avoiding_set_ff0) \<Longrightarrow>
  (\<And>t pd p. (t, pd) \<in> set3_\<tau>_pre x' \<union> set4_\<tau>_pre x' \<Longrightarrow> UFVars_ff0 t (pd p) \<subseteq> FFVars_\<tau> t \<union> PFVars_ff0 p \<union> avoiding_set_ff0) \<Longrightarrow>
  imsupp u \<inter> (FFVars_\<tau> (\<tau>_ctor (map_\<tau>_pre id id fst fst x)) \<union> PFVars_ff0 p \<union> avoiding_set_ff0) = {} \<Longrightarrow> u ` set2_\<tau>_pre x \<inter> set2_\<tau>_pre x = {} \<Longrightarrow>
  imsupp u' \<inter> (FFVars_\<tau> (\<tau>_ctor (map_\<tau>_pre id id fst fst x')) \<union> PFVars_ff0 p \<union> avoiding_set_ff0) = {} \<Longrightarrow> u' ` set2_\<tau>_pre x' \<inter> set2_\<tau>_pre x' = {} \<Longrightarrow>
  mr_rel_\<tau>_pre (inv u' \<circ> u) (inv u' \<circ> u) (\<lambda>(t, pd) (t', pd'). rrename_\<tau> u t = rrename_\<tau> u' t' \<and> PUmap_ff0 u t pd = PUmap_ff0 u' t' pd') (\<lambda>(t, pd) (t', pd'). rrename_\<tau> u t = rrename_\<tau> u' t' \<and> PUmap_ff0 u t pd = PUmap_ff0 u' t' pd') x x' \<Longrightarrow>
  Uctor_ff0 x p = Uctor_ff0 x' p"
apply (rule trans)
   apply (rule Uctor_rename)
       apply assumption+
  apply (rule sym[THEN trans[rotated]])
   apply (rule Uctor_rename)
       apply (rotate_tac 2)
       apply assumption+
  apply (rule arg_cong2[OF _ refl, of _ _ Uctor_ff0])
  apply (rule iffD2[OF fun_cong[OF fun_cong[OF \<tau>_pre.mr_rel_eq[symmetric]]]])
  apply (rule iffD2[OF \<tau>_pre.mr_rel_map(1)])
        apply (assumption | rule supp_id_bound bij_id)+
  unfolding id_o OO_eq
  apply (rule iffD2[OF \<tau>_pre.mr_rel_map(3)])
         apply assumption+
  unfolding relcompp_conversep_Grp
  unfolding Grp_def in_UNIV_simp prod_case_lam_simp prod.inject
  apply (rule \<tau>_pre.mr_rel_mono_strong)
       apply (assumption | rule supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv)+
  apply (raw_tactic \<open>let val ctxt = @{context} in EVERY1 [
    REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
    Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      let val [thm1, thm2] = map ((fn ct => infer_instantiate' context [SOME ct] @{thm prod.exhaust}) o snd) params
      in rtac context thm1 1 THEN rtac context thm2 1 end
    ) ctxt,
    hyp_subst_tac ctxt,
    K (unfold_thms_tac ctxt @{thms prod.case}),
    etac ctxt conjE,
    rtac ctxt conjI,
    rtac ctxt sym,
    assume_tac ctxt,
    rtac ctxt sym,
    assume_tac ctxt
  ] end\<close>)+
  done

lemma CTOR_ff0_cong: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> bij (u'::'a \<Rightarrow> 'a) \<Longrightarrow> |supp u'| <o |UNIV::'a set| \<Longrightarrow>
  (\<And>t pd p. (t, pd) \<in> set3_\<tau>_pre x \<union> set4_\<tau>_pre x \<Longrightarrow> UFVars'_ff0 t (pd p) \<subseteq> FVars_\<tau> t \<union> PFVars_ff0 p \<union> avoiding_set_ff0) \<Longrightarrow>
  (\<And>t pd p. (t, pd) \<in> set3_\<tau>_pre x' \<union> set4_\<tau>_pre x' \<Longrightarrow> UFVars'_ff0 t (pd p) \<subseteq> FVars_\<tau> t \<union> PFVars_ff0 p \<union> avoiding_set_ff0) \<Longrightarrow>
  imsupp u \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst x)) \<union> PFVars_ff0 p \<union> avoiding_set_ff0) = {} \<Longrightarrow> u ` set2_\<tau>_pre x \<inter> set2_\<tau>_pre x = {} \<Longrightarrow>
  imsupp u' \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst x')) \<union> PFVars_ff0 p \<union> avoiding_set_ff0) = {} \<Longrightarrow> u' ` set2_\<tau>_pre x' \<inter> set2_\<tau>_pre x' = {} \<Longrightarrow>
  mr_rel_\<tau>_pre (inv u' \<circ> u) (inv u' \<circ> u) (\<lambda>(t, pd) (t', pd'). alpha_\<tau> (rename_\<tau> u t) (rename_\<tau> u' t') \<and> PUmap'_ff0 u t pd = PUmap'_ff0 u' t' pd') (\<lambda>(t, pd) (t', pd'). alpha_\<tau> (rename_\<tau> u t) (rename_\<tau> u' t') \<and> PUmap'_ff0 u t pd = PUmap'_ff0 u' t' pd') x x' \<Longrightarrow>
  CTOR_ff0 x p = CTOR_ff0 x' p"
  unfolding CTOR_ff0_def
  apply (rule Uctor_cong)
            apply assumption
           apply assumption
          apply (rotate_tac 2)
          apply assumption+
  unfolding \<tau>_pre.set_map[OF id_prems] image_Un[symmetric]
        apply (drule exists_map_prod_id, erule exE, erule conjE,
      raw_tactic \<open>hyp_subst_tac @{context} 1 THEN SELECT_GOAL (unfold_thms_tac @{context} @{thms UFVars'_ff0_def[symmetric] \<tau>.alpha_FVarss[OF \<tau>.TT_alpha_quotient_syms, unfolded fun_cong[OF meta_eq_to_obj_eq[OF FFVars_\<tau>_def], symmetric], symmetric]}) 1\<close>,
      assumption)+
  apply (raw_tactic \<open>
    let
      val ctxt = @{context}
      val common_tac = EVERY' [
        REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
        rtac ctxt @{thm relcomppI},
        rtac ctxt refl,
        hyp_subst_tac ctxt,
        SELECT_GOAL (unfold_thms_tac @{context} @{thms comp_def}),
        rtac ctxt @{thm \<tau>.TT_Quotient_rep_abss}
      ];
    in EVERY1 [
      rtac ctxt trans,
      rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<inter>)"]},
      REPEAT_DETERM o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
      K (assume_tac ctxt 2),
      K (unfold_thms_tac ctxt @{thms FFVars_\<tau>_def \<tau>_ctor_def}),
      rtac ctxt @{thm \<tau>.alpha_FVarss},
      rtac ctxt @{thm \<tau>.alpha_transs},
      rtac ctxt @{thm \<tau>.TT_Quotient_rep_abss},
      rtac ctxt @{thm alpha_\<tau>.intros},
      rtac ctxt @{thm bij_id},
      rtac ctxt @{thm supp_id_bound},
      rtac ctxt @{thm id_on_id},
      K (unfold_thms_tac ctxt @{thms \<tau>_pre.map_comp[OF id_prems id_prems] o_id comp_assoc[symmetric] fst_comp_map_prod[symmetric] \<tau>.rename_ids}),
      rtac ctxt @{thm iffD2[OF \<tau>_pre.mr_rel_map(1)]},
      REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
      K (unfold_thms_tac ctxt @{thms id_o}),
      rtac ctxt @{thm iffD2[OF \<tau>_pre.mr_rel_map(3)]},
      REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
      K (unfold_thms_tac ctxt @{thms inv_o_simp1[OF bij_id] relcompp_conversep_Grp}),
      K (unfold_thms_tac ctxt @{thms Grp_UNIV_def}),
      rtac ctxt @{thm \<tau>_pre.mr_rel_mono_strong},
      REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
      rtac ctxt @{thm iffD2[OF fun_cong[OF fun_cong[OF \<tau>_pre.mr_rel_eq]]]},
      rtac ctxt refl,
      REPEAT_DETERM o common_tac,
      K (unfold_thms_tac ctxt @{thms image_id}),
      assume_tac ctxt
    ] end\<close>)+
  apply (rule iffD2[OF \<tau>_pre.mr_rel_map(1)])
        apply (assumption | rule supp_id_bound bij_id supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv)+
  apply (rule iffD2[OF \<tau>_pre.mr_rel_map(3)])
         apply (assumption | rule supp_id_bound bij_id supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv)+
  unfolding relcompp_conversep_Grp inv_id id_o o_id
  unfolding Grp_UNIV_def
  apply (rule \<tau>_pre.mr_rel_mono_strong)
       apply (assumption | rule supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv)+
  apply (raw_tactic \<open>let val ctxt = @{context} in EVERY1 [
    REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
    Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      let val [thm1, thm2] = map ((fn ct => infer_instantiate' context [SOME ct] @{thm prod.exhaust}) o snd) params
      in rtac context thm1 1 THEN rtac context thm2 1 end
    ) ctxt,
    hyp_subst_tac ctxt,
    K (unfold_thms_tac ctxt @{thms prod.case}),
    rtac ctxt @{thm relcomppI},
    resolve_tac ctxt @{thms fun_cong[OF map_prod_def] prod.case},
    K (unfold_thms_tac ctxt @{thms prod.case map_prod_def}),
    etac ctxt conjE,
    rtac ctxt conjI,
    K (unfold_thms_tac ctxt @{thms rrename_\<tau>_def}),
    rtac ctxt @{thm iffD2[OF \<tau>.TT_Quotient_total_abs_eq_iffs]},
    rtac ctxt @{thm \<tau>.alpha_transs},
    rtac ctxt @{thm iffD2[OF \<tau>.alpha_bij_eqs]},
    REPEAT_DETERM o assume_tac ctxt,
    rtac ctxt @{thm \<tau>.TT_Quotient_rep_abss},
    rtac ctxt @{thm \<tau>.alpha_transs[rotated]},
    rtac ctxt @{thm \<tau>.alpha_syms},
    rtac ctxt @{thm iffD2[OF \<tau>.alpha_bij_eqs]},
    REPEAT_DETERM o assume_tac ctxt,
    rtac ctxt @{thm \<tau>.TT_Quotient_rep_abss},
    assume_tac ctxt,
    SELECT_GOAL (unfold_thms_tac @{context} @{thms PUmap_ff0_def PUmap'_ff0_def id_def Umap'_ff0_def}),
    assume_tac ctxt
  ] end\<close>)+
  done

lemma Umap'_ff0_alpha: "alpha_\<tau> t t' \<Longrightarrow> Umap'_ff0 u t = Umap'_ff0 u t'"
  unfolding Umap'_ff0_def
  apply (rule arg_cong2[OF refl, of _ _ Umap_ff0])
  apply (rule iffD2[OF \<tau>.TT_Quotient_total_abs_eq_iffs])
  apply assumption
  done

lemma PUmap'_ff0_alpha: "alpha_\<tau> t t' \<Longrightarrow> PUmap'_ff0 u t = PUmap'_ff0 u t'"
  unfolding PUmap'_ff0_def
  apply (rule arg_cong[of _ _ "\<lambda>f. (\<lambda>pu p. f (pu (Pmap_ff0 (inv u) p)))", OF Umap'_ff0_alpha])
  apply assumption
  done

lemma int_empty:
  assumes "suitable_ff0 pick" "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a)" "|supp u| <o |UNIV::'a set|" "imsupp u \<inter> avoiding_set_ff0 = {}"
  shows "set2_\<tau>_pre (XXl_ff0 pick u p x) \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst (XXl_ff0 pick u p x))) \<union> PFVars_ff0 p \<union> avoiding_set_ff0) = {}"
    "set2_\<tau>_pre (XXr_ff0 pick u p x) \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst (XXr_ff0 pick u p x))) \<union> PFVars_ff0 p \<union> avoiding_set_ff0) = {}"
  by (raw_tactic \<open>
    let
      val prems = @{thms assms}
      val ctxt = @{context}
      val mrbnf = tau
      val u = @{term u}

      val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf
      val live = MRBNF_Def.live_of_mrbnf mrbnf
      val [suitable_ff0, bij, supp, imsupp] = prems
      val t = Term.abs ("x", pre_T) (FVars_t $ (ctor_t $ Bound 0))
      val pick_prems = map (fn thm => thm OF [suitable_ff0]) @{thms pick_prems}
      val bij_comps = swapped @{thm bij_comp} (hd pick_prems) bij
      val supp_comps = map (fn thm => thm OF @{thms infinite_var_\<tau>_pre}) (
        swapped @{thm supp_comp_bound} (nth pick_prems 1) supp
      );
      val set_maps = maps (fn thm => map2 (fn a => fn b => thm OF (mk_prems [supp] [a, b] var_types)) bij_comps supp_comps) (
        MRBNF_Def.set_map_of_mrbnf mrbnf
      );
      val rename_ct = Thm.cterm_of ctxt (rename_t $ u)
      val set_map_syms = map (fn thm => infer_instantiate' ctxt (replicate live (SOME rename_ct)) (
        thm OF (mk_prems [supp] [bij, supp] var_types)
      ) RS sym) (MRBNF_Def.set_map_of_mrbnf mrbnf);

      val comp_FVars = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt FVars_t)] @{thm comp_def}
      val FVars_renames = maps (fn thm => map2 (fn a => fn b => thm OF [a, b]) (bij::bij_comps) (supp::supp_comps)) @{thms \<tau>.FVars_renames}
      val diff_images = map (fn b => @{thm image_set_diff[OF bij_is_inj]} OF [b] RS sym) bij_comps

      fun solve_tac XX_def inv = EVERY' [
        rtac ctxt trans,
        rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<inter>)"]},
        REPEAT_DETERM o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] arg_cong),
        K (unfold_thms_tac ctxt [XX_def]),
        rtac ctxt (MRBNF_Def.map_comp_of_mrbnf mrbnf),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ bij_comps @ supp_comps),
        K (unfold_thms_tac ctxt (@{thms id_o o_id comp_def[of fst] fst_conv})),
        SELECT_GOAL (unfold_thms_tac ctxt (@{thms \<tau>.FVars_ctors image_comp image_UN[symmetric]}
          @ set_maps @ [comp_FVars] @ FVars_renames @ diff_images)
        ),
        K (unfold_thms_tac ctxt (@{thms image_comp[symmetric] image_Un[symmetric] \<tau>.FVars_ctors[symmetric]} @ [
          @{thm id_on_image[OF pick_id_on]} OF [suitable_ff0],
          @{thm id_on_image[OF pick_id_on_image]} OF [suitable_ff0, bij, supp]
        ])),
        (if inv then
          rtac ctxt (@{thm iffD1[OF inj_image_eq_iff[OF bij_is_inj[OF bij_imp_bij_inv]]]} OF [bij])
        else K all_tac),
        K (unfold_thms_tac ctxt (@{thms image_empty image_Un} @ [
          @{thm image_Int[OF bij_is_inj[OF bij_imp_bij_inv]]} OF [bij],
          @{thm id_on_image[OF id_on_inv[OF _ imsupp_id_on]]} OF [bij, imsupp],
          @{thm image_inv_f_f[OF bij_is_inj]} OF [bij],
          @{thm ff0.PFVars_Pmap[OF bij_imp_bij_inv supp_inv_bound, symmetric]} OF [bij, bij, supp]
        ])),
        Method.insert_tac ctxt [Local_Defs.unfold0 ctxt @{thms suitable_ff0_def} suitable_ff0],
        REPEAT_DETERM o eresolve_tac ctxt [allE, conjE],
        assume_tac ctxt ORELSE' EVERY' [
          K (unfold_thms_tac ctxt (@{thms \<tau>.FVars_ctors image_Un image_UN image_comp[symmetric]} @ [
            @{thm image_set_diff[OF bij_is_inj]} OF [bij],
            infer_instantiate' ctxt [SOME rename_ct] comp_FVars RS sym
          ] @ map (fn thm => thm RS sym) FVars_renames @ set_map_syms)),
          K (unfold_thms_tac ctxt @{thms \<tau>.FVars_ctors[symmetric]}),
          assume_tac ctxt
        ]
      ];
    in EVERY1 [
      K (unfold_thms_tac ctxt @{thms atomize_conj}),
      rtac ctxt conjI,
      solve_tac @{thm XXl_ff0_def} true,
      solve_tac @{thm XXr_ff0_def} false
    ] end
  \<close>)

ML \<open>
val f_t = @{term "f_ff0 :: _ \<Rightarrow> 'a::var_\<tau>_pre raw_\<tau> \<Rightarrow> _ \<Rightarrow> _"}
val P = @{typ "'a::var_\<tau>_pre ssfun"}
val U = @{typ "'a::var_\<tau>_pre \<tau>"}
val A = HOLogic.mk_prodT (raw_T, P --> U)
val UFVars'_ff0_t = @{term "UFVars'_ff0 :: _ \<Rightarrow> 'a::var_\<tau>_pre \<tau> \<Rightarrow> _"}
val avoiding_set = @{term "avoiding_set_ff0 :: 'a::var_\<tau>_pre set"}

val map_id_fst_t = Term.list_comb (
  MRBNF_Def.mk_map_of_mrbnf [] [A, A] [raw_T, raw_T] vars vars tau,
  MRBNF_Def.interlace [BNF_Util.fst_const A, BNF_Util.fst_const A] (map HOLogic.id_const vars) (map HOLogic.id_const vars) var_types
)
\<close>

lemma f_UFVars'_ff0:
  assumes "suitable_ff0 pick"
  shows "UFVars'_ff0 t (f_ff0 pick t p) \<subseteq> FVars_\<tau> t \<union> PFVars_ff0 p \<union> avoiding_set_ff0"
  by (raw_tactic \<open>
    let
      val prems = @{thms assms}
      val ctxt = @{context}
      val mrbnf = tau
      val pick = @{term pick}
      val t = @{term t}

      val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf
      val id_prems = mk_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound} var_types
      val pick_prems = map (fn thm => thm OF prems) @{thms pick_prems}
      val id_pick_prems = mk_prems @{thms supp_id_bound} pick_prems var_types
      val P_t = Term.abs ("t", raw_T) (HOLogic.mk_all ("p", P, BNF_Util.mk_leq
        (UFVars'_ff0_t $ Bound 1 $ (f_t $ pick $ Bound 1 $ Bound 0))
        (MRBNF_Util.mk_Un (MRBNF_Util.mk_Un (FVars_t $ Bound 1, PFVars_t $ Bound 0), avoiding_set))
      ));
      val thm = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt P_t), SOME (Thm.cterm_of ctxt t)] @{thm \<tau>.TT_subshape_induct}
      val map_comp = MRBNF_Def.map_comp_of_mrbnf mrbnf OF (id_pick_prems @ id_prems)

    in EVERY1 [
      rtac ctxt (allE OF [thm]),
      K (assume_tac ctxt 2),
      rtac ctxt allI,
      Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
        rtac context (infer_instantiate' context [SOME (snd (hd params))] @{thm raw_\<tau>.exhaust}) 1
      ) ctxt,
      hyp_subst_tac ctxt,
      rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]]},
      REPEAT_DETERM o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
      Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
        let
          val [_, p, x] = map (Thm.term_of o snd) params
          val pick_t = pick $ x $ p
          val bindRec = Term.abs ("t", raw_T) (HOLogic.mk_prod (
            rename_t $ pick_t $ Bound 0,
            f_t $ pick $ (rename_t $ pick_t $ Bound 0)
          ));
          val otherRec = Term.abs ("t", raw_T) (HOLogic.pair_const raw_T (P --> U) $ Bound 0 $ (f_t $ pick $ Bound 0));
          val t = ctor_t $ (map_id_fst_t $ (
            Term.list_comb (MRBNF_Def.mk_map_of_mrbnf [] [raw_T, raw_T] [A, A] vars vars mrbnf,
              MRBNF_Def.interlace [bindRec, otherRec] [pick_t] (map HOLogic.id_const vars) var_types
            ) $ x
          ));
        in rtac context (infer_instantiate' context [NONE, SOME (Thm.cterm_of context t)] @{thm \<tau>.alpha_FVarss}) 1 end
      ) ctxt,
      K (unfold_thms_tac ctxt ([MRBNF_Def.map_comp_of_mrbnf mrbnf OF (id_pick_prems @ id_prems)] @ @{thms id_o comp_def[of fst] fst_conv id_def[symmetric]})),
      resolve_tac ctxt @{thms alpha_\<tau>.intros},
      Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
        rtac context (infer_instantiate' context [SOME (snd (nth params 2)), SOME (snd (nth params 1))] (hd pick_prems)) 1
      ) ctxt,
      resolve_tac ctxt pick_prems,
      rtac ctxt (@{thm pick_id_on} OF prems),
      rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems),
      K (unfold_thms_tac ctxt (@{thms Grp_UNIV_id conversep_eq OO_eq inv_id id_o relcompp_conversep_Grp} @ [
        @{thm inv_o_simp1} OF [hd pick_prems], @{thm f_ff0_simp} OF prems
      ])),
      K (unfold_thms_tac ctxt [MRBNF_Def.mr_rel_def_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]),
      rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
      resolve_tac ctxt @{thms \<tau>.alpha_refls},
      resolve_tac ctxt @{thms \<tau>.alpha_refls},
      K (unfold_thms_tac ctxt ([map_comp] @ @{thms id_o o_id})),
      K (unfold_thms_tac ctxt @{thms comp_def}),
      rtac ctxt @{thm subset_trans},
      rtac ctxt @{thm UFVars'_CTOR},
      Method.insert_tac ctxt prems,
      K (unfold_thms_tac ctxt (map (fn thm => thm OF id_pick_prems) (MRBNF_Def.set_map_of_mrbnf mrbnf) @ @{thms suitable_ff0_def Int_Un_empty})),
      REPEAT_DETERM o eresolve_tac ctxt [allE, conjE],
      assume_tac ctxt,
      etac ctxt UnE,
      K (unfold_thms_tac ctxt @{thms image_prod_f_g}),
      etac ctxt conjE,
      hyp_subst_tac ctxt,
      dresolve_tac ctxt @{thms \<tau>.set_subshape_images[rotated -1]},
      resolve_tac ctxt pick_prems,
      resolve_tac ctxt pick_prems,
      Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
        rtac ctxt (@{thm allE} OF [hd prems OF [nth prems 1]]) 1
      ) ctxt,
      assume_tac ctxt,
      dtac ctxt @{thm iffD1[OF image_prod_f_g[of _ _ id, unfolded image_id, unfolded id_def]]},
      etac ctxt conjE,
      hyp_subst_tac ctxt,
      dresolve_tac ctxt @{thms \<tau>.set_subshapes},
      Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
        rtac context (infer_instantiate' context [NONE, SOME (snd (snd (split_last params)))] @{thm spec}) 1
      ) ctxt,
      Goal.assume_rule_tac ctxt,
      K (unfold_thms_tac ctxt ([map_comp] @ @{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]})),
      rtac ctxt @{thm subset_refl}
    ] end\<close>)

ML \<open>
val Umap'_ff0_t = @{term "Umap'_ff0 :: _ \<Rightarrow> _ \<Rightarrow> 'a::var_\<tau>_pre \<tau> \<Rightarrow> _"}
val CTOR_ff0_t = @{term "CTOR :: _ \<Rightarrow> _ \<Rightarrow> 'a::var_\<tau>_pre \<tau>"}
val Pmap_ff0 = @{term "Pmap_ff0 :: ('a::var_\<tau>_pre \<Rightarrow> 'a) \<Rightarrow> _ \<Rightarrow> _"}
val XXl_ff0_t = @{term "XXl_ff0 :: _ \<Rightarrow>_ \<Rightarrow> 'a::var_\<tau>_pre ssfun \<Rightarrow> _"}
val XXr_ff0_t = @{term "XXr_ff0 :: _ \<Rightarrow>_ \<Rightarrow> 'a::var_\<tau>_pre ssfun \<Rightarrow> _"}
val FVars_t = @{term "FVars_\<tau> :: 'a::var_\<tau>_pre raw_\<tau> \<Rightarrow> _"}
val ctor_t = @{term "raw_\<tau>_ctor :: _ \<Rightarrow> 'a::var_\<tau>_pre raw_\<tau>"}
val PUmap'_ff0_t = @{term "PUmap'_ff0 :: _ \<Rightarrow> 'a::var_\<tau>_pre raw_\<tau> \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _"}
val suitable_ff0_t = @{term "suitable_ff0 :: (_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'a::var_\<tau>_pre) => _"}
val alpha_t = @{term "alpha_\<tau> :: 'a::var_\<tau>_pre raw_\<tau> \<Rightarrow> _ \<Rightarrow> _"}

fun mk_imsupp u =
  let val T = fastype_of u
  in Const (@{const_name imsupp}, T --> HOLogic.mk_setT (fst (dest_funT T))) $ u end;

fun topBindSet T = nth (MRBNF_Def.mk_sets_of_mrbnf (replicate 4 [])
  (replicate 4 [T, T])
  (replicate 4 vars) (replicate 4 vars)
   tau) 1
\<close>

lemma imsupp_id_on_XX:
  assumes "suitable_ff0 pick" "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a)" "|supp u| <o |UNIV::'a set|"
  shows "imsupp w \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst (XXl_ff0 pick u p x))) \<union> PFVars_ff0 p \<union> avoiding_set_ff0) = {} \<Longrightarrow>
    id_on (u ` set1_\<tau>_pre x) w \<and> id_on (u ` (\<Union> (FVars_\<tau> ` set3_\<tau>_pre x) - set2_\<tau>_pre x)) w \<and> id_on (u ` \<Union> (FVars_\<tau> ` set4_\<tau>_pre x)) w"
  "imsupp w' \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst (XXr_ff0 pick u p x))) \<union> PFVars_ff0 p \<union> avoiding_set_ff0) = {} \<Longrightarrow>
    id_on (u ` set1_\<tau>_pre x) w' \<and> id_on (u ` (\<Union> (FVars_\<tau> ` set3_\<tau>_pre x) - set2_\<tau>_pre x)) w' \<and> id_on (u ` \<Union> (FVars_\<tau> ` set4_\<tau>_pre x)) w'"
  by (raw_tactic \<open>
    let
      val ctxt = @{context}
      val prems = @{thms assms}
      val mrbnf = tau

      val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf
      val [suitable_ff0, bij, supp] = prems
      val pick_prems = map (fn thm => thm OF [suitable_ff0]) @{thms pick_prems}
      val id_prems = mk_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound} var_types
      val bij_comps = swapped @{thm bij_comp} (hd pick_prems) bij
      val supp_comps = swapped @{thm supp_comp_bound[OF _ _ infinite_var_\<tau>_pre]} (nth pick_prems 1) supp
      val map_comps = map2 (fn b => fn s => MRBNF_Def.map_comp_of_mrbnf mrbnf OF (mk_prems [supp] [b, s] var_types @ id_prems)) bij_comps supp_comps
      val set_maps = maps (fn thm => map2 (fn b => fn s => thm OF (mk_prems [supp] [b, s] var_types)) bij_comps supp_comps) (
        MRBNF_Def.set_map_of_mrbnf mrbnf
      );
      val comp_FVars = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt FVars_t)] @{thm comp_def}
      val FVars_renames = maps (fn thm => map2 (fn b => fn s => thm OF [b, s]) (bij::bij_comps) (supp::supp_comps)) @{thms \<tau>.FVars_renames}
      val image_diffs = map (fn b => @{thm image_set_diff[OF bij_is_inj]} OF [b] RS sym) bij_comps

    in EVERY [
      unfold_thms_tac ctxt @{thms atomize_conj atomize_imp},
      rtac ctxt conjI 1,
      unfold_thms_tac ctxt (@{thms XXl_ff0_def XXr_ff0_def id_o comp_def[of fst] fst_conv \<tau>.FVars_ctors image_comp}
        @ map_comps @ set_maps @ [comp_FVars]
      ),
      unfold_thms_tac ctxt (@{thms image_UN[symmetric]} @ FVars_renames @ image_diffs),
      unfold_thms_tac ctxt (@{thms image_comp[symmetric] Int_Un_distrib Un_empty} @ [
        @{thm id_on_image[OF pick_id_on]} OF [suitable_ff0],
        @{thm id_on_image[OF pick_id_on_image]} OF [suitable_ff0, bij, supp]
      ]),
      ALLGOALS (EVERY' [
        rtac ctxt impI,
        REPEAT_DETERM o etac ctxt conjE,
        REPEAT_DETERM o EVERY' [
          TRY o rtac ctxt conjI,
          rtac ctxt @{thm imsupp_id_on},
          assume_tac ctxt
        ]
      ])
    ] end\<close>)

lemma alpha_ctor_pick:
  assumes "suitable_ff0 pick"
    shows "alpha_\<tau> (raw_\<tau>_ctor x) (raw_\<tau>_ctor (
  map_\<tau>_pre id id fst fst (
    map_\<tau>_pre id (pick x p) (\<lambda>t. (rename_\<tau> (pick x p) t, f_ff0 pick (rename_\<tau> (pick x p) t))) (\<lambda>t. (t, f_ff0 pick t)) x
  )))"
  by (raw_tactic \<open>
    let
      val ctxt = @{context}
      val prems = @{thms assms}
      val suitable_ff0 = @{thm assms}
      val mrbnf = tau

      val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf
      val pick_prems = map (fn thm => thm OF prems)  @{thms pick_prems}
      val id_pick_prems = mk_prems @{thms supp_id_bound} pick_prems var_types
      val id_pick_prems' = mk_prems @{thms bij_id supp_id_bound} pick_prems var_types
      val id_prems = mk_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound} var_types
      val map_comps = [MRBNF_Def.map_comp_of_mrbnf mrbnf OF (id_pick_prems @ id_prems)]
  in EVERY1 [
    rtac ctxt (@{thm alpha_\<tau>.intros} OF pick_prems),
    rtac ctxt (@{thm pick_id_on} OF [suitable_ff0]),
    SELECT_GOAL (unfold_thms_tac ctxt (@{thms inv_id id_o o_id comp_def[of fst] fst_conv relcompp_conversep_Grp} @ map_comps @ [
      nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2 OF (id_pick_prems @ id_pick_prems')
    ])),
    rtac ctxt (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf OF id_prems),
    REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound infinite_var_\<tau>_pre supp_id_bound bij_imp_bij_inv supp_inv_bound} @ pick_prems),
    rtac ctxt (iffD2 OF [@{thm fun_cong[OF fun_cong]} OF [MRBNF_Def.mr_rel_eq_of_mrbnf mrbnf], refl]),
    REPEAT_DETERM o (
      resolve_tac ctxt (@{thms \<tau>.alpha_refls} @ [ballI, impI, refl, fun_cong OF [@{thm inv_o_simp1} OF [hd pick_prems] RS sym]])
      ORELSE' hyp_subst_tac ctxt
    )
  ] end\<close>)

lemma f_swap_alpha:
  assumes "suitable_ff0 pick" "suitable_ff0 pick'" "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a)" "|supp u| <o |UNIV::'a set|" "imsupp u \<inter> avoiding_set_ff0 = {}" "alpha_\<tau> t t'"
  shows "f_ff0 pick (rename_\<tau> u t) = PUmap'_ff0 u t (f_ff0 pick t) \<and> f_ff0 pick t = f_ff0 pick' t'"
  apply (raw_tactic \<open>
    let
      val ctxt = @{context}
      val mrbnf = tau
      val pick = @{term pick}
      val pick' = @{term pick'}
      val t = @{term t}

      fun mk_all (s, T) t = HOLogic.mk_all (s, T, t)
      val mk_int = HOLogic.mk_binop @{const_name inf}

      val u = Free ("u", hd vars --> hd vars);
      val P_t = Term.abs ("t", raw_T) (fold_rev mk_all [("pick", fastype_of pick), ("pick'", fastype_of pick'), ("p", P), ("t'", raw_T), ("u", hd vars --> hd vars)] (
        fold_rev (curry HOLogic.mk_imp) [
          suitable_ff0_t $ Bound 4, suitable_ff0_t $ Bound 3, MRBNF_Util.mk_bij u,
          MRBNF_Util.mk_ordLess (MRBNF_Util.mk_card_of (MRBNF_Util.mk_supp u)) (MRBNF_Util.mk_card_of (HOLogic.mk_UNIV (hd vars))),
          HOLogic.mk_eq (mk_int (mk_imsupp u, avoiding_set), Const (@{const_name bot}, HOLogic.mk_setT (hd vars))),
          alpha_t $ Bound 5 $ Bound 1
        ] (
          HOLogic.mk_conj (
            HOLogic.mk_eq (f_t $ Bound 4 $ (rename_t $ Bound 0 $ Bound 5) $ Bound 2, PUmap'_ff0_t $ Bound 0 $ Bound 5 $ (f_t $ Bound 4 $ Bound 5) $ Bound 2),
            HOLogic.mk_eq (f_t $ Bound 4 $ Bound 5, f_t $ Bound 3 $ Bound 1)
          )
        )
      ));
      val thm = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt P_t), SOME (Thm.cterm_of ctxt t)] @{thm \<tau>.TT_subshape_induct}

    in EVERY1 [
      rtac ctxt (allE OF [thm]),
      REPEAT_DETERM o resolve_tac ctxt [allI, impI],
      Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
        rtac context (infer_instantiate' context [SOME (snd (hd params))] @{thm raw_\<tau>.exhaust}) 1
      ) ctxt,
      hyp_subst_tac ctxt,
      Subgoal.FOCUS (fn {context=ctxt, prems, params, ...} =>
        let
          val [_, pick, pick', p, t', u, x] = map (Thm.term_of o snd) params
          val [IH, suitable_ff0, suitable_ff0', bij, supp, imsupp, alpha] = prems

          val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf
          val pick_prems = map (fn thm => thm OF [suitable_ff0]) @{thms pick_prems}
          val id_pick_prems = mk_prems @{thms supp_id_bound} pick_prems var_types
          val id_pick_prems' = mk_prems @{thms bij_id supp_id_bound} pick_prems var_types
          val id_prems = mk_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound} var_types
          val bij_comps = swapped @{thm bij_comp} bij (hd pick_prems)
          val supp_comps = swapped @{thm supp_comp_bound[OF _ _ infinite_var_\<tau>_pre]} supp (nth pick_prems 1)
          val (bij_inv, supp_inv) = (@{thm bij_imp_bij_inv} OF [bij], @{thm supp_inv_bound} OF [bij, supp])

          val rec_t = Term.abs ("t", raw_T) (HOLogic.pair_const raw_T (P --> U) $ Bound 0 $ (f_t $ pick $ Bound 0))
          val fA_t = Term.abs ("x", fastype_of x) (Term.list_comb (XXl_ff0_t, [pick, u, p, Bound 0]))
          val fB_t = Term.abs ("x", fastype_of x) (Term.list_comb (XXr_ff0_t, [pick, u, p, Bound 0]))
          val fA_T = snd (dest_funT (fastype_of fA_t))
          val g_t = Term.abs ("x'", fA_T) (MRBNF_Util.mk_Un (MRBNF_Util.mk_Un (
            FVars_t $ (ctor_t $ (map_id_fst_t $ Bound 0)),
            PFVars_t $ p),
            avoiding_set)
          );

          val map_comp = MRBNF_Def.map_comp_of_mrbnf mrbnf
          val map_comps = [
            map_comp OF (id_pick_prems @ id_prems),
            map_comp OF (mk_prems [supp] [bij, supp] var_types @ id_pick_prems),
            map_comp OF (id_pick_prems @ mk_prems [supp] [bij, supp] var_types)
          ] @ map2 (fn b => fn s => map_comp OF (mk_prems [supp] [b, s] var_types @ id_prems)) bij_comps supp_comps;
          val rename_comp0s = map (fn thm => thm OF ([bij, supp] @ pick_prems)) @{thms \<tau>.rename_comp0s};
          val rename_comps = maps (fn thm => [thm OF (pick_prems @ [bij, supp]), thm OF ([bij, supp] @ pick_prems)]) @{thms \<tau>.rename_comps}
          val comp_rec = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt rec_t)] @{thm comp_def};
          val exists_bij_betw = infer_instantiate' ctxt [
            NONE, NONE, SOME (Thm.cterm_of ctxt (topBindSet A)), SOME (Thm.cterm_of ctxt fA_t),
            SOME (Thm.cterm_of ctxt x), SOME (Thm.cterm_of ctxt g_t), NONE, SOME (Thm.cterm_of ctxt fB_t)
          ] @{thm exists_bij_betw_refl[OF infinite_var_\<tau>_pre]};
          val set_maps = maps (fn thm => map2 (fn b => fn s => thm OF (mk_prems [supp] [b, s] var_types)) bij_comps supp_comps) (
            MRBNF_Def.set_map_of_mrbnf mrbnf
          );

        val eq_fun_tac = EVERY' [
          rotate_tac ~2,
          dtac ctxt @{thm UN_I},
          assume_tac ctxt,
          rotate_tac ~1,
          Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
            let
              val z = Thm.term_of (snd (snd (split_last params)));
              val set = nth (MRBNF_Def.mk_sets_of_mrbnf (replicate 4 []) (replicate 4 [raw_T, raw_T]) (replicate 4 vars) (replicate 4 vars) tau) 1
              val ct = Thm.cterm_of context (HOLogic.mk_mem (z, set $ x));
              val thm = Local_Defs.unfold0 context @{thms eq_True eq_False} (
                infer_instantiate' context [SOME ct] @{thm bool.exhaust}
              );
            in rtac ctxt thm 1 end
          ) ctxt,
          dtac ctxt @{thm eq_onD},
          assume_tac ctxt,
          assume_tac ctxt,
          dtac ctxt @{thm DiffI},
          assume_tac ctxt,
          rotate_tac ~1,
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            let
              val [v, w, a, z] = map (Thm.term_of o snd) params
              fun mk_arg_cong t = infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] arg_cong
            in EVERY1 [
              K (unfold_thms_tac ctxt @{thms comp_def}),
              REPEAT_DETERM o dresolve_tac ctxt (map (fn thm => thm OF [suitable_ff0, bij, supp]) @{thms imsupp_id_on_XX}),
              REPEAT_DETERM o etac ctxt conjE,
              rtac ctxt trans,
              rtac ctxt trans,
              rtac ctxt (mk_arg_cong v),
              rtac ctxt (mk_arg_cong u),
              dtac ctxt @{thm id_onD[rotated]},
              rtac ctxt (@{thm pick_id_on} OF [suitable_ff0]),
              assume_tac ctxt,
              dtac ctxt imageI,
              rotate_tac ~1,
              rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt v)] @{thm id_onD[rotated]}),
              assume_tac ctxt,
              assume_tac ctxt,
              rtac ctxt sym,
              dtac ctxt imageI,
              rotate_tac ~1,
              rtac ctxt trans,
              rtac ctxt trans,
              rtac ctxt (mk_arg_cong w),
              dtac ctxt @{thm id_onD[rotated]},
              rtac ctxt (@{thm pick_id_on_image} OF [suitable_ff0, bij, supp]),
              assume_tac ctxt,
              rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt w)] @{thm id_onD[rotated]}),
              assume_tac ctxt,
              assume_tac ctxt,
              rtac ctxt refl
            ] end
          ) ctxt,
          resolve_tac ctxt @{thms \<tau>.alpha_refls}
        ];

        val nonbinding_fun_eq_tac = EVERY' [
          resolve_tac ctxt @{thms \<tau>.alpha_bijs},
          REPEAT_DETERM o assume_tac ctxt,
          rtac ctxt ballI,
          K (unfold_thms_tac ctxt [@{thm \<tau>.FVars_renames} OF [bij, supp]]),
          rotate_tac ~2,
          dtac ctxt @{thm UN_I},
          assume_tac ctxt,
          rotate_tac ~1,
          K (unfold_thms_tac ctxt @{thms image_UN[symmetric]}),
          REPEAT_DETERM o (
            dresolve_tac ctxt (map (fn thm => thm OF [suitable_ff0, bij, supp]) @{thms imsupp_id_on_XX}) THEN'
            REPEAT_DETERM o etac ctxt conjE
          ),
          rtac ctxt trans,
          dtac ctxt @{thm id_onD[rotated]},
          assume_tac ctxt,
          assume_tac ctxt,
          rtac ctxt sym,
          dtac ctxt @{thm id_onD[rotated]},
          rotate_tac ~3,
          assume_tac ctxt,
          assume_tac ctxt,
          resolve_tac ctxt @{thms \<tau>.alpha_refls}
        ];

        in EVERY1 [
          rtac ctxt conjI,
          rtac ctxt trans,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt f_t)] @{thm arg_cong3[OF refl _ refl]}),
          resolve_tac ctxt (map (fn thm => thm OF [bij, supp]) @{thms \<tau>.rename_simps}),
          rtac ctxt (trans OF [@{thm f_ff0_simp} OF [suitable_ff0]]),
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt @{thm fun_cong[OF fun_cong[OF PUmap'_ff0_alpha]]},
          rtac ctxt (@{thm alpha_ctor_pick} OF [suitable_ff0]),
          K (unfold_thms_tac ctxt @{thms PUmap'_ff0_def}),
          rtac ctxt trans,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt Umap'_ff0_t)] @{thm arg_cong3[OF refl refl]}),
          rtac ctxt (trans OF [@{thm f_ff0_simp} OF [suitable_ff0]]),
          SELECT_GOAL (unfold_thms_tac ctxt (@{thms id_o o_id} @ map_comps)),
          K (unfold_thms_tac ctxt [comp_rec]),
          rtac ctxt refl,
          rtac ctxt trans,
          rtac ctxt (@{thm Umap'_CTOR} OF [bij, supp]),
          K (unfold_thms_tac ctxt (@{thms id_def[symmetric] id_o o_id comp_pair XXl_ff0_def[symmetric] XXr_ff0_def[symmetric]} @ rename_comp0s @ [
            fun_cong OF [@{thm ff0.Pmap_comp0[unfolded comp_def]} OF [bij, supp, bij_inv, supp_inv]] RS sym, comp_rec,
            @{thm inv_simp2} OF [bij], @{thm fun_cong[OF ff0.Pmap_id0, unfolded id_def, unfolded id_def[symmetric]]}
          ] @ map_comps @ rename_comps)),
          rtac ctxt (exE OF [Drule.rotate_prems 2 exists_bij_betw]),
          REPEAT_DETERM_N 2 o EVERY' [
            rtac ctxt @{thm \<tau>_pre.Un_bound},
            resolve_tac ctxt @{thms \<tau>_pre.set_bd_UNIV},
            rtac ctxt @{thm \<tau>_pre.Un_bound},
            rtac ctxt @{thm \<tau>_pre.Un_bound},
            rtac ctxt @{thm \<tau>.card_of_FVars_bounds},
            rtac ctxt @{thm ff0.small_PFVars},
            rtac ctxt @{thm ff0.small_avoiding_sets},
            resolve_tac ctxt (map (fn thm => thm OF [suitable_ff0, bij, supp, imsupp]) @{thms int_empty}),
            SELECT_GOAL (unfold_thms_tac ctxt (@{thms XXl_ff0_def XXr_ff0_def} @ set_maps)),
            rtac ctxt refl
          ],
          REPEAT_DETERM o resolve_tac ctxt bij_comps,
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          rtac ctxt @{thm CTOR_ff0_cong},
          assume_tac ctxt,
          assume_tac ctxt,
          rotate_tac 4,
          assume_tac ctxt,
          assume_tac ctxt,
          REPEAT_DETERM_N 2 o EVERY' [
            REPEAT_DETERM o resolve_tac ctxt [allI, impI],
            SELECT_GOAL (unfold_thms_tac ctxt (@{thms XXl_ff0_def XXr_ff0_def id_o o_id comp_def[of fst] fst_conv} @ map_comps @ set_maps)),
            etac ctxt UnE,
            K (unfold_thms_tac ctxt @{thms image_prod_f_g'}),
            REPEAT_DETERM o EVERY' [
              REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
              hyp_subst_tac ctxt,
              TRY o EVERY' [
                dresolve_tac ctxt ([nth @{thms \<tau>.set_subshapes} 1] @ map (fn thm => thm OF pick_prems) [hd @{thms \<tau>.set_subshape_images[OF _ _ imageI]}]),
                dtac ctxt IH,
                REPEAT_DETERM o etac ctxt allE,
                EVERY' (map (fn thm => etac ctxt impE THEN' rtac ctxt thm) [suitable_ff0, suitable_ff0', bij, supp, imsupp, @{thm \<tau>.alpha_refls}]),
                dtac ctxt (conjunct1 RS sym),
                rtac ctxt (iffD2 OF @{thms arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]}),
                rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt UFVars'_ff0_t)] @{thm arg_cong2[OF refl]}),
                assume_tac ctxt
              ],
              SELECT_GOAL (unfold_thms_tac ctxt rename_comps),
              rtac ctxt (@{thm f_UFVars'_ff0} OF [suitable_ff0])
            ]
          ],
          REPEAT_DETERM o assume_tac ctxt,
          rtac ctxt (iffD2 OF [@{thm arg_cong2[OF meta_eq_to_obj_eq meta_eq_to_obj_eq]} OF @{thms XXl_ff0_def XXr_ff0_def}]),
          rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
          REPEAT_DETERM o resolve_tac ctxt ([supp] @ bij_comps @ supp_comps),
          REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv}),
          rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
          REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv} @ [bij, supp] @ pick_prems)),
          K (unfold_thms_tac ctxt (@{thms relcompp_conversep_Grp} @ [MRBNF_Def.mr_rel_def_of_mrbnf mrbnf])),
          rtac ctxt (iffD2 OF [MRBNF_Def.rel_cong_of_mrbnf mrbnf]),
          rtac ctxt (MRBNF_Def.map_cong0_of_mrbnf mrbnf),
          REPEAT_DETERM o FIRST' [
            resolve_tac ctxt @{thms supp_id_bound bij_id},
            assume_tac ctxt,
            resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv} @ [bij, supp] @ pick_prems)
          ],

          rtac ctxt @{thm inv_id_middle},
          rtac ctxt bij,
          rotate_tac ~1,
          dtac ctxt imageI,
          rotate_tac ~1,
          REPEAT_DETERM o dresolve_tac ctxt (map (fn thm => thm OF [suitable_ff0, bij, supp]) @{thms imsupp_id_on_XX}),
          REPEAT_DETERM o etac ctxt conjE,
          rtac ctxt trans,
          rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
          dtac ctxt @{thm id_onD[rotated]},
          assume_tac ctxt,
          assume_tac ctxt,
          REPEAT_DETERM o (dtac ctxt @{thm id_on_inv[rotated]} THEN' assume_tac ctxt),
          dtac ctxt @{thm id_onD[rotated]},
          assume_tac ctxt,
          assume_tac ctxt,

          rtac ctxt @{thm inv_id_middle2},
          resolve_tac ctxt bij_comps,
          assume_tac ctxt,
          dtac ctxt @{thm eq_onD},
          assume_tac ctxt,
          rtac ctxt sym,
          assume_tac ctxt,

          REPEAT_DETERM o rtac ctxt refl,
          K (unfold_thms_tac ctxt [MRBNF_Def.map_id_of_mrbnf mrbnf]),
          rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),

          (* binding set *)
          rtac ctxt @{thm relcomppI},
          rtac ctxt @{thm iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]]},
          rtac ctxt refl,
          K (unfold_thms_tac ctxt @{thms prod.case}),
          rtac ctxt conjI,
          rtac ctxt (iffD2 OF [infer_instantiate' ctxt (replicate 4 NONE @ [SOME (Thm.cterm_of ctxt alpha_t)]) @{thm arg_cong2}]),
          REPEAT_DETERM o EVERY' [
            resolve_tac ctxt @{thms \<tau>.rename_comps},
            resolve_tac ctxt bij_comps,
            resolve_tac ctxt supp_comps,
            assume_tac ctxt,
            assume_tac ctxt
          ],
          resolve_tac ctxt @{thms \<tau>.alpha_bijs},
          REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (bij_comps @ supp_comps @ @{thms supp_comp_bound bij_comp infinite_var_\<tau>_pre})),
          rtac ctxt ballI,
          eq_fun_tac,
          rotate_tac ~1,
          rtac ctxt trans,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt PUmap'_ff0_t)] @{thm arg_cong3[OF refl refl]}),
          rtac ctxt ext,
          dresolve_tac ctxt (map (fn thm => thm OF pick_prems) @{thms \<tau>.set_subshape_images[OF _ _ imageI]}),
          dtac ctxt IH,
          REPEAT_DETERM o etac ctxt allE,
          EVERY' (map (fn thm => etac ctxt impE THEN' rtac ctxt thm) [suitable_ff0, suitable_ff0', bij, supp, imsupp, @{thm \<tau>.alpha_refls}]),
          dtac ctxt (conjunct1 RS sym),
          assume_tac ctxt,
          rtac ctxt trans,
          SELECT_GOAL (unfold_thms_tac ctxt rename_comps),
          rtac ctxt ext,
          dresolve_tac ctxt (map (fn thm => thm OF [nth bij_comps 1, nth supp_comps 1]) @{thms \<tau>.set_subshape_images[OF _ _ imageI]}),
          dtac ctxt IH,
          REPEAT_DETERM o etac ctxt allE,
          REPEAT_DETERM o (etac ctxt impE THEN' (rtac ctxt suitable_ff0 ORELSE' assume_tac ctxt)),
          etac ctxt impE,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt,
          etac ctxt impE,
          resolve_tac ctxt @{thms \<tau>.alpha_refls},
          dtac ctxt (conjunct1 RS sym),
          assume_tac ctxt,
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt ext,
          forward_tac ctxt (map (fn thm => thm OF [hd bij_comps, hd supp_comps]) @{thms \<tau>.set_subshape_images[OF _ _ imageI]}),
          dtac ctxt IH,
          REPEAT_DETERM o etac ctxt allE,
          rotate_tac 4,
          REPEAT_DETERM o (etac ctxt impE THEN' (rtac ctxt suitable_ff0 ORELSE' assume_tac ctxt)),
          etac ctxt impE,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt,
          etac ctxt impE,
          resolve_tac ctxt @{thms \<tau>.alpha_refls},
          dtac ctxt (conjunct1 RS sym),
          assume_tac ctxt,
          rtac ctxt trans,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt f_t)] @{thm arg_cong2[OF refl]}),
          resolve_tac ctxt @{thms \<tau>.rename_comps},
          resolve_tac ctxt bij_comps,
          resolve_tac ctxt supp_comps,
          assume_tac ctxt,
          assume_tac ctxt,
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt f_t)] @{thm arg_cong2[OF refl]}),
          resolve_tac ctxt @{thms \<tau>.rename_comps},
          resolve_tac ctxt bij_comps,
          resolve_tac ctxt supp_comps,
          assume_tac ctxt,
          assume_tac ctxt,
          forward_tac ctxt @{thms \<tau>.set_subshape_images[OF _ _ imageI, rotated -1]},
          rtac ctxt @{thm bij_comp},
          rtac ctxt (nth bij_comps 1),
          assume_tac ctxt,
          rtac ctxt @{thm supp_comp_bound},
          resolve_tac ctxt supp_comps,
          assume_tac ctxt,
          rtac ctxt @{thm infinite_var_\<tau>_pre},
          dtac ctxt IH,
          REPEAT_DETERM o etac ctxt allE,
          EVERY' (map (fn thm => etac ctxt impE THEN' rtac ctxt thm) [suitable_ff0, suitable_ff0, bij, supp, imsupp]),
          etac ctxt impE,
          K (prefer_tac 2),
          dtac ctxt conjunct2,
          assume_tac ctxt,
          resolve_tac ctxt @{thms \<tau>.alpha_bijs},
          REPEAT_DETERM o FIRST' [
            resolve_tac ctxt (bij_comps @ supp_comps),
            assume_tac ctxt,
            resolve_tac ctxt @{thms bij_comp supp_comp_bound infinite_var_\<tau>_pre}
          ],
          rtac ctxt ballI,
          eq_fun_tac,

          (* nonbinding set *)
          rtac ctxt @{thm relcomppI},
          rtac ctxt @{thm iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]]},
          rtac ctxt refl,
          K (unfold_thms_tac ctxt @{thms prod.case}),
          rtac ctxt conjI,

          nonbinding_fun_eq_tac,

          rtac ctxt trans,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt PUmap'_ff0_t)] @{thm arg_cong3[OF refl refl]}),
          rtac ctxt ext,
          dresolve_tac ctxt @{thms \<tau>.set_subshapes},
          dtac ctxt IH,
          REPEAT_DETERM o etac ctxt allE,
          EVERY' (map (fn thm => etac ctxt impE THEN' rtac ctxt thm) [suitable_ff0, suitable_ff0', bij, supp, imsupp, @{thm \<tau>.alpha_refls}]),
          dtac ctxt (conjunct1 RS sym),
          assume_tac ctxt,
          rtac ctxt trans,
          rtac ctxt ext,
          rotate_tac ~1,
          dresolve_tac ctxt (map (fn thm => thm OF [bij, supp]) @{thms \<tau>.set_subshape_images[OF _ _ imageI]}),
          dtac ctxt IH,
          REPEAT_DETERM o etac ctxt allE,
          EVERY' (map (fn thm => etac ctxt impE THEN' rtac ctxt thm) [suitable_ff0, suitable_ff0']),
          etac ctxt impE,
          assume_tac ctxt,
          etac ctxt impE,
          assume_tac ctxt,
          etac ctxt impE,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt,
          etac ctxt impE,
          resolve_tac ctxt @{thms \<tau>.alpha_refls},
          dtac ctxt (conjunct1 RS sym),
          assume_tac ctxt,
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt ext,
          rotate_tac ~1,
          dresolve_tac ctxt (map (fn thm => thm OF [bij, supp]) @{thms \<tau>.set_subshape_images[OF _ _ imageI]}),
          dtac ctxt IH,
          REPEAT_DETERM o etac ctxt allE,
          EVERY' (map (fn thm => etac ctxt impE THEN' rtac ctxt thm) [suitable_ff0, suitable_ff0']),
          etac ctxt impE,
          rotate_tac 4,
          assume_tac ctxt,
          etac ctxt impE,
          assume_tac ctxt,
          etac ctxt impE,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt,
          etac ctxt impE,
          resolve_tac ctxt @{thms \<tau>.alpha_refls},
          dtac ctxt (conjunct1 RS sym),
          assume_tac ctxt,
          REPEAT_DETERM o EVERY' [
            rtac ctxt sym,
            rtac ctxt trans,
            rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt f_t)] @{thm arg_cong2[OF refl]}),
            resolve_tac ctxt @{thms \<tau>.rename_comps},
            rtac ctxt bij,
            rtac ctxt supp,
            assume_tac ctxt,
            assume_tac ctxt
          ],
          rotate_tac ~1,
          forward_tac ctxt @{thms \<tau>.set_subshape_images[OF _ _ imageI, rotated -1]},
          rtac ctxt @{thm bij_comp},
          rtac ctxt bij,
          rotate_tac 4,
          assume_tac ctxt,
          REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (bij :: supp :: @{thms supp_comp_bound infinite_var_\<tau>_pre})),
          dtac ctxt IH,
          REPEAT_DETERM o etac ctxt allE,
          EVERY' (map (fn thm => etac ctxt impE THEN' rtac ctxt thm) [suitable_ff0, suitable_ff0, bij, supp, imsupp]),
          etac ctxt impE,
          K (prefer_tac 2),
          dtac ctxt conjunct2,
          assume_tac ctxt,
          rtac ctxt (iffD2 OF [infer_instantiate' ctxt (replicate 4 NONE @ [SOME (Thm.cterm_of ctxt alpha_t)]) @{thm arg_cong2}]),
          REPEAT_DETERM o EVERY' [
            resolve_tac ctxt @{thms \<tau>.rename_comps[symmetric]},
            rtac ctxt bij,
            rtac ctxt supp,
            assume_tac ctxt,
            assume_tac ctxt
          ],
          resolve_tac ctxt @{thms \<tau>.alpha_syms},
          nonbinding_fun_eq_tac

          (* f pick t = f pick' t' *)
        ] end
      ) ctxt
    ] end\<close>)


   apply (rule ext)
   apply (rule alpha_\<tau>.cases)
    apply assumption
   apply (drule iffD1[OF raw_\<tau>.inject])
   apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)

  subgoal premises prems for _ pick pick' _ t' u x p w z z'
    thm prems
    unfolding f_ff0_simp[OF prems(2)] f_ff0_simp[OF prems(3)] \<tau>_pre.map_comp[OF supp_id_bound pick_prems[OF prems(2)] id_prems]
      \<tau>_pre.map_comp[OF supp_id_bound pick_prems[OF prems(3)] id_prems] id_o o_id
    unfolding comp_def
    apply (rule exE[OF exists_bij_betw[OF infinite_var_\<tau>_pre,
            of "pick z p" "pick' z' p" w set2_\<tau>_pre z' z set2_\<tau>_pre
            "\<lambda>x. map_\<tau>_pre id id fst fst (map_\<tau>_pre id (pick' z' p) (\<lambda>x. (rename_\<tau> (pick' z' p) x, f_ff0 pick' (rename_\<tau> (pick' z' p) x))) (\<lambda>t. (t, f_ff0 pick' t)) x)"
            "\<lambda>x. FVars_\<tau> (raw_\<tau>_ctor x) \<union> PFVars_ff0 p \<union> avoiding_set_ff0"
            "\<lambda>x. map_\<tau>_pre id id fst fst (map_\<tau>_pre id (pick z p) (\<lambda>x. (rename_\<tau> (pick z p) x, f_ff0 pick (rename_\<tau> (pick z p) x))) (\<lambda>t. (t, f_ff0 pick t)) x)"
            ]])
             apply (rule pick_prems[OF prems(2)])
              apply (rule pick_prems[OF prems(3)])
            apply (rule prems)
           apply (rule \<tau>_pre.mr_rel_set(2)[OF supp_id_bound prems(8,9,11)])
          apply (raw_tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>) (* Trivial *)
         prefer 3
         apply (raw_tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>) (* Trivial *)
    unfolding \<tau>_pre.set_map[OF id_prems] image_id
      \<tau>_pre.set_map[OF supp_id_bound pick_prems[OF prems(2)]]
      \<tau>_pre.set_map[OF supp_id_bound pick_prems[OF prems(3)]]
      \<tau>.alpha_FVarss[OF \<tau>.alpha_syms[OF alpha_ctor_pick[OF prems(2)]]]
      \<tau>.alpha_FVarss[OF \<tau>.alpha_syms[OF alpha_ctor_pick[OF prems(3)]]]
        apply (rule allE[OF prems(3)[unfolded suitable_ff0_def]], (erule allE conjE)+, assumption)
       apply (rule refl)
      apply (rule allE[OF prems(2)[unfolded suitable_ff0_def]], (erule allE conjE)+, assumption)
     apply (rule refl)
    apply (erule exE conjE)+
    apply (rule CTOR_ff0_cong)
            apply (rotate_tac 4)
              apply assumption
             apply assumption
            apply assumption
           apply assumption
    unfolding \<tau>_pre.set_map[OF supp_id_bound pick_prems[OF prems(2)]]
          apply (erule UnE)
    unfolding image_prod_f_g
           apply (erule conjE)
           apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
           apply (rule f_UFVars'_ff0[OF prems(2)])
    unfolding image_prod_f_g'
          apply (erule exE conjE)+
          apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
          apply (rule f_UFVars'_ff0[OF prems(2)])

      (* repeat but for pick' *)
    unfolding \<tau>_pre.set_map[OF supp_id_bound pick_prems[OF prems(3)]]
         apply (erule UnE)
    unfolding image_prod_f_g
          apply (erule conjE)
          apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
          apply (rule f_UFVars'_ff0[OF prems(3)])
    unfolding image_prod_f_g'
         apply (erule exE conjE)+
         apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule f_UFVars'_ff0[OF prems(3)])
    unfolding \<tau>.alpha_FVarss[OF \<tau>.alpha_syms[OF alpha_ctor_pick[OF prems(2)]]]
      \<tau>.alpha_FVarss[OF \<tau>.alpha_syms[OF alpha_ctor_pick[OF prems(3)]]]
        apply assumption
       apply assumption
      apply assumption
     apply assumption

    (* mr_rel *)
    apply (rule iffD2[OF \<tau>_pre.mr_rel_map(1)[OF supp_id_bound pick_prems[OF prems(2)]]])
       apply (rule supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv | assumption)+
    unfolding id_o o_id
    apply (rule iffD2[OF \<tau>_pre.mr_rel_map(3)])
           apply (rule supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp pick_prems[OF prems(2)] bij_imp_bij_inv bij_id supp_id_bound pick_prems[OF prems(3)] | assumption)+
    unfolding inv_id id_o o_id relcompp_conversep_Grp
    apply (rule \<tau>_pre.mr_rel_mono_strong0[OF _ _ _ _ _ _ prems(11)])
             apply (rule supp_id_bound prems supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp pick_prems[OF prems(2)] bij_imp_bij_inv pick_prems[OF prems(3)] | assumption)+
       apply (rule ballI)
       apply (rule sym)
       apply (rule trans)
        apply (rule trans)
         apply (rule comp_apply)
        apply (rule arg_cong[of _ _ "inv _"])
        apply (rotate_tac 4)
        apply (drule imsupp_id_on)
        apply (drule id_onD)
    apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms \<tau>.FVars_ctors}) 1\<close>)
         apply (rule UnI1)+
         apply assumption
        apply assumption
       apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms \<tau>.alpha_FVarss[OF prems(7), symmetric]}) 1\<close>)
       apply (drule imsupp_id_on)
       apply (drule id_on_inv[rotated])
        apply assumption
       apply (drule id_onD)
        apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms \<tau>.FVars_ctors}) 1\<close>)
        apply (rule UnI1)+
        apply assumption
       apply (rule trans)
        apply assumption
       apply (rule id_apply[symmetric])

      apply (rule ballI)
      apply (rule sym)
      apply (rule trans)
    apply (rule trans)
       apply (rule comp_apply)
       apply (rule trans)
        apply (rule arg_cong[of _ _ "inv _"])
    apply (rule trans)
        apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms comp_assoc}) 1\<close>)
    apply (rule trans)
          apply (rule comp_apply)
         apply (rule arg_cong[of _ _ "inv _"])
         apply (rule trans)
        apply (drule eq_onD)
           apply assumption
        apply (rule sym)
          apply assumption
         apply (rule comp_apply)
        apply (rule inv_simp1)
        apply assumption
       apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms comp_def}) 1\<close>)
       apply (rule inv_simp1)
       apply (rule pick_prems[OF prems(3)])
      apply (rule refl)

     apply (rule ballI impI)+
     apply (rule relcomppI)
      apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Grp_UNIV_def}) 1\<close>)
      apply (rule refl)
    unfolding prod.case
     apply (rule conjI)
      apply (rule iffD2[OF arg_cong2[of _ _ _ _ alpha_\<tau>]])
        apply (rule \<tau>.rename_comps)
           apply (rule pick_prems[OF prems(2)] | assumption)+
       apply (rule \<tau>.rename_comps)
          apply (rule pick_prems[OF prems(3)] | assumption)+
      apply (rule \<tau>.alpha_transs)
       apply (rule \<tau>.alpha_bijs)
            apply (raw_tactic \<open>REPEAT_DETERM (match_tac @{context} @{thms bij_comp pick_prems[OF prems(2)] supp_comp_bound infinite_var_\<tau>_pre} 1 ORELSE eq_assume_tac 1)\<close>)
          apply (rule bij_comp)
           apply (rule prems(8))
    apply (rule bij_comp)
           apply (rule pick_prems[OF prems(3)])
          apply assumption
         apply (rule supp_comp_bound prems pick_prems[OF prems(3)] infinite_var_\<tau>_pre | assumption)+

(* start same_fun_tac *)
        apply (rule ballI)
    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      let
        val params' = map (Thm.term_of o snd) params
        val s = nth (MRBNF_Def.mk_sets_of_mrbnf (replicate 4 []) (replicate 4 [raw_T, raw_T]) (replicate 4 vars) (replicate 4 vars) tau) 1
        val thm = infer_instantiate' context [SOME (Thm.cterm_of context (HOLogic.mk_mem (nth params' 4, s $ @{term z})))] @{thm bool.exhaust}
        val thm' = Local_Defs.unfold0 context @{thms eq_True eq_False} thm
      in rtac context thm' 1 end
    ) @{context} 1\<close>)
         apply (drule eq_onD)
          apply assumption
         apply (rule sym)
         apply assumption
        apply (rotate_tac -5)
        apply (frule UN_I)
         apply (rotate_tac 2)
         apply assumption
        apply (rotate_tac -1)
        apply (drule DiffI)
         apply assumption
        apply (rule trans)
         apply (rule trans[OF comp_apply])
    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      rtac context (infer_instantiate' context [NONE, NONE, SOME (snd (nth params 1))] arg_cong) 1
    ) @{context} 1\<close>)
         apply (drule id_onD[OF pick_id_on[OF prems(2)]])
         apply assumption
        apply (rule trans)
    apply (rotate_tac 8)
         apply (drule imsupp_id_on)
         apply (drule id_onD)
          apply (rule UnI1)
    apply (rule UnI1)
        apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms \<tau>.FVars_ctors}) 1\<close>)
          apply (rule UnI1)
          apply (rule UnI2)
          apply assumption
         apply assumption
        apply (rule sym)
        apply (rule trans)
         apply (rule trans)
          apply (rule comp_apply)
         apply (rule arg_cong[of _ _ "_ \<circ> _"])
         apply (drule id_onD[OF prems(10)])
         apply assumption
        apply (rule trans)
         apply (rule comp_apply)
    apply (rule trans)
apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      rtac context (infer_instantiate' context [NONE, NONE, SOME (snd (hd params))] arg_cong) 1
    ) @{context} 1\<close>)
         apply (rotate_tac 3)
         apply (drule iffD2[OF inj_image_mem_iff[OF bij_is_inj], rotated])
          apply (rule prems(8))
    apply (raw_tactic \<open>unfold_thms_tac @{context} @{thms \<tau>.FVars_renames[OF prems(8,9), symmetric] \<tau>.alpha_FVarss}\<close>)
         apply (rotate_tac -3)
         apply (frule UN_I)
    apply (rotate_tac 2)
          apply assumption
         apply (rotate_tac -1)
    unfolding arg_cong2[OF refl arg_cong[OF \<tau>_pre.mr_rel_set(2)[OF supp_id_bound prems(8,9,11)], of "(`) (inv w)", unfolded image_comp inv_o_simp1[OF prems(8)] image_id, symmetric], of "(\<in>)"]
      image_in_bij_eq[OF bij_imp_bij_inv[OF prems(8)], unfolded inv_inv_eq[OF prems(8)]]
       apply (drule DiffI)
          apply assumption
         apply (rotate_tac -1)
         apply (drule iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"], rotated])
          apply (drule id_onD[OF prems(10)])
          apply assumption
         apply (rotate_tac -1)
         apply (drule id_onD[OF pick_id_on[OF prems(3)]])
         apply assumption
    unfolding \<tau>.alpha_FVarss[OF prems(7), symmetric]
        apply (drule imsupp_id_on)
        apply (drule id_onD)
         apply (rule UnI1)
    apply (rule UnI1)
    unfolding \<tau>.FVars_ctors
         apply (rule UnI1)
         apply (rule UnI2)
         apply assumption
        apply assumption
(* end same_fun_tac *)

       apply (rule \<tau>.alpha_refls)
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ alpha_\<tau>]])
       apply (rule \<tau>.rename_comps[symmetric])
          apply (rule prems bij_comp pick_prems[OF prems(3)] supp_comp_bound infinite_var_\<tau>_pre | assumption)+
      apply (rule iffD2[OF \<tau>.alpha_bij_eqs])
        apply (rule prems bij_comp pick_prems[OF prems(3)] supp_comp_bound infinite_var_\<tau>_pre | assumption)+
     apply (frule \<tau>.set_subshape_images[OF pick_prems[OF prems(2)] imageI])
     apply (rule ext)
     apply (drule prems(1))
     apply (erule allE)+
     apply (erule impE, rule prems(2))
     apply (erule impE, rule prems(3))
     apply (rotate_tac 4)
     apply (erule impE, assumption)+
     apply (erule impE)
      apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
      apply (erule conjE)+
      apply assumption
     apply (erule impE, rule \<tau>.alpha_refls)
    apply (drule conjunct1)
     apply (rule trans)
      apply (rule sym)
      apply assumption
     apply (rule trans)
      apply (rule arg_cong3[OF refl _ refl, of _ _ f_ff0])
      apply (rule \<tau>.rename_comps[OF pick_prems[OF prems(2)]])
       apply assumption+
     apply (rule trans)
      apply (frule \<tau>.set_subshape_images[OF _ _ imageI, rotated -1])
        apply (rule bij_comp)
         apply (rule pick_prems[OF prems(2)])
        apply assumption
       apply (rule supp_comp_bound)
         apply (rule pick_prems[OF prems(2)])
        apply assumption
       apply (rule infinite_var_\<tau>_pre)
      apply (drule prems(1))
      apply (erule allE)+
      apply (erule impE, rule prems(2))
      apply (erule impE, rule prems(3))
      apply (erule impE, rule prems)+
      apply (erule impE)
    prefer 2
       apply (drule conjunct2)
       apply (rotate_tac -1)
    apply (drule fun_cong)
       apply assumption
      apply (rule \<tau>.alpha_bijs)
            apply (raw_tactic \<open>REPEAT_DETERM (match_tac @{context} @{thms bij_comp pick_prems[OF prems(2)] supp_comp_bound infinite_var_\<tau>_pre} 1 ORELSE eq_assume_tac 1)\<close>)
         apply (rule bij_comp)
          apply (rule prems(8))
         apply (rule bij_comp)
          apply (rule pick_prems[OF prems(3), of z' p])
         apply (rotate_tac -5)
         apply assumption
        apply (rule supp_comp_bound prems pick_prems[OF prems(3)] infinite_var_\<tau>_pre | assumption)+

    apply (rotate_tac -5)
(* same_fun_tac again *)
       apply (rule ballI)
    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      let
        val param = snd (split_last (map (Thm.term_of o snd) params))
        val s = nth (MRBNF_Def.mk_sets_of_mrbnf (replicate 4 []) (replicate 4 [raw_T, raw_T]) (replicate 4 vars) (replicate 4 vars) tau) 1
        val thm = infer_instantiate' context [SOME (Thm.cterm_of context (HOLogic.mk_mem (param, s $ @{term z})))] @{thm bool.exhaust}
        val thm' = Local_Defs.unfold0 context @{thms eq_True eq_False} thm
      in rtac context thm' 1 end
    ) @{context} 1\<close>)
         apply (drule eq_onD)
          apply assumption
         apply (rule sym)
         apply assumption
        apply (rotate_tac -5)
        apply (frule UN_I)
         apply (rotate_tac 2)
         apply assumption
        apply (rotate_tac -1)
        apply (drule DiffI)
         apply assumption
        apply (rule trans)
         apply (rule trans[OF comp_apply])
    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      rtac context (infer_instantiate' context [NONE, NONE, SOME (snd (nth params 1))] arg_cong) 1
    ) @{context} 1\<close>)
         apply (drule id_onD[OF pick_id_on[OF prems(2)]])
         apply assumption
        apply (rule trans)
    apply (rotate_tac 8)
         apply (drule imsupp_id_on)
         apply (drule id_onD)
         apply (rule UnI1)
    apply (rule UnI1)
        apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms \<tau>.FVars_ctors}) 1\<close>)
          apply (rule UnI1)
          apply (rule UnI2)
          apply assumption
         apply assumption
        apply (rule sym)
        apply (rule trans)
         apply (rule trans)
          apply (rule comp_apply)
         apply (rule arg_cong[of _ _ "_ \<circ> _"])
         apply (drule id_onD[OF prems(10)])
         apply assumption
        apply (rule trans)
         apply (rule comp_apply)
    apply (rule trans)
apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      rtac context (infer_instantiate' context [NONE, NONE, SOME (snd (hd params))] arg_cong) 1
    ) @{context} 1\<close>)
         apply (rotate_tac 3)
         apply (drule iffD2[OF inj_image_mem_iff[OF bij_is_inj], rotated])
          apply (rule prems(8))
    apply (raw_tactic \<open>unfold_thms_tac @{context} @{thms \<tau>.FVars_renames[OF prems(8,9), symmetric] \<tau>.alpha_FVarss}\<close>)
         apply (rotate_tac -3)
         apply (frule UN_I)
    apply (rotate_tac 2)
          apply assumption
         apply (rotate_tac -1)
    unfolding arg_cong2[OF refl arg_cong[OF \<tau>_pre.mr_rel_set(2)[OF supp_id_bound prems(8,9,11)], of "(`) (inv w)", unfolded image_comp inv_o_simp1[OF prems(8)] image_id, symmetric], of "(\<in>)"]
      image_in_bij_eq[OF bij_imp_bij_inv[OF prems(8)], unfolded inv_inv_eq[OF prems(8)]]
       apply (drule DiffI)
          apply assumption
         apply (rotate_tac -1)
         apply (drule iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"], rotated])
          apply (drule id_onD[OF prems(10)])
          apply assumption
         apply (rotate_tac -1)
         apply (drule id_onD[OF pick_id_on[OF prems(3)]])
         apply assumption
    unfolding \<tau>.alpha_FVarss[OF prems(7), symmetric]
        apply (drule imsupp_id_on)
        apply (drule id_onD)
        apply (rule UnI1)
    apply (rule UnI1)
    unfolding \<tau>.FVars_ctors
         apply (rule UnI1)
         apply (rule UnI2)
         apply assumption
             apply assumption
    (* end same_fun_tac *)

     apply (rule \<tau>.alpha_refls)
      apply (frule \<tau>.set_subshape_images[OF _ _ imageI, rotated -1])
        apply (rule bij_comp)
    apply (rule prems(8))
         apply (rule pick_prems[OF prems(3)])
       apply (rule supp_comp_bound prems pick_prems[OF prems(3)] infinite_var_\<tau>_pre)+
      apply (drule prems(1))
      apply (erule allE)+
      apply (erule impE, rule prems(3))+
      apply (rotate_tac 8)
      apply (erule impE, assumption)+
    apply (erule impE)
      apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
      apply (erule conjE)+
       apply assumption
      apply (erule impE)
       prefer 2
    apply (erule conjE)
       apply (rule trans)
        apply (rule trans)
         apply (rule arg_cong3[OF refl _ refl, of _ _ f_ff0])
    unfolding comp_assoc
         apply (rule \<tau>.rename_comps[symmetric])
            apply (rule bij_comp prems pick_prems[OF prems(3)] supp_comp_bound infinite_var_\<tau>_pre)+
          apply assumption
         apply assumption
        apply assumption
    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      rtac context (infer_instantiate' context [NONE, NONE, SOME (snd (nth params 4))] fun_cong) 1
    ) @{context} 1\<close>)
       apply (rule trans)
        apply (rule arg_cong3[OF refl refl, of _ _ PUmap'_ff0])
        apply assumption
       apply (rule fun_cong[OF PUmap'_ff0_alpha])
       apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ alpha_\<tau>]])
        apply (rule \<tau>.rename_comps[symmetric])
           apply (rule prems pick_prems[OF prems(3)])+
       apply (rule iffD2[OF \<tau>.alpha_bij_eqs[OF pick_prems[OF prems(3)]]])
       apply assumption
        apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ alpha_\<tau>]])
        apply (rule \<tau>.rename_comps[symmetric])
           apply (rule prems pick_prems[OF prems(3)])+
       apply (rule iffD2[OF \<tau>.alpha_bij_eqs[OF pick_prems[OF prems(3)]]])
       apply assumption


    (* nonbinding set *)
    apply (rule ballI impI)+
    apply (rule relcomppI)
    unfolding Grp_UNIV_def
     apply (rule refl)
    unfolding prod.case
    apply (rule conjI)
     apply (rule \<tau>.alpha_bijs)
          apply assumption+

(* start nonbinding_fun_eq_tac *)
      apply (rule ballI)
      apply (rotate_tac -4)
      apply (frule UN_I)
       apply (rotate_tac 3)
       apply assumption
      apply (rule trans)
       apply (rotate_tac -4)
       apply (drule imsupp_id_on)
       apply (drule id_onD)
        apply (rule UnI1)
        apply (rule UnI1)
        apply (rule UnI2)
        apply assumption
       apply assumption
      apply (rule sym)
      apply (drule imsupp_id_on)
      apply (drule id_onD)
       apply (rule UnI1)
       apply (rule UnI1)
       apply (rule UnI2)
       apply assumption
      apply assumption
  (* end nonbinding_fun_eq_tac *)
     apply assumption

    apply (rule ext)
    apply (rule trans)
     apply (drule \<tau>.set_subshapes)
     apply (drule prems(1))
     apply (erule allE)+
     apply (erule impE, rule prems(2))
     apply (erule impE, rule prems(3))
     apply (rotate_tac 4)
     apply (erule impE, assumption)+
     apply (erule impE)
      apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
      apply (erule conjE)+
      apply assumption
     apply (erule impE, rule \<tau>.alpha_refls)
     apply (drule conjunct1[THEN sym])
     apply assumption
    apply (rule trans)
     apply (frule \<tau>.set_subshape_images[OF _ _ imageI, rotated -1])
    apply (rotate_tac 4)
    apply assumption+
     apply (drule prems(1))
     apply (erule allE)+
     apply (erule impE, rule prems(2))
     apply (erule impE, rule prems(3))
     apply (erule impE, rule prems)+
     apply (erule impE)

      apply (rule \<tau>.alpha_bijs)
    apply assumption+
(* start nonbinding_fun_eq_tac *)
      apply (rule ballI)
      apply (rotate_tac -4)
      apply (frule UN_I)
       apply (rotate_tac 3)
       apply assumption
      apply (rule trans)
       apply (rotate_tac -4)
       apply (drule imsupp_id_on)
       apply (drule id_onD)
        apply (rule UnI1)
        apply (rule UnI1)
        apply (rule UnI2)
        apply assumption
       apply assumption
      apply (rule sym)
      apply (drule imsupp_id_on)
      apply (drule id_onD)
       apply (rule UnI1)
       apply (rule UnI1)
       apply (rule UnI2)
       apply assumption
      apply assumption
  (* end nonbinding_fun_eq_tac *)
    apply (rule \<tau>.alpha_refls)

      apply (drule conjunct2)
      apply (rule fun_cong[of "f_ff0 _ _"])
     apply assumption
    apply (rule trans)
     apply (frule \<tau>.set_subshapes)
     apply (drule prems(1))
     apply (erule allE)+
     apply (erule impE, (rule prems(3) | assumption))+
     apply (erule impE)
      apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
      apply (erule conjE)+
    apply assumption
     apply (erule impE)
      apply (rule \<tau>.alpha_refls)
     apply (drule conjunct1)
     apply assumption
    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      rtac context (infer_instantiate' context [NONE, NONE, SOME (snd (nth params 4))] fun_cong) 1
    ) @{context} 1\<close>)
    apply (rule trans)
     apply (rule arg_cong3[OF refl refl, of _ _ PUmap'_ff0])
     apply (drule \<tau>.set_subshapes)
     apply (drule prems(1))
    apply (erule allE)+
     apply (erule impE, rule prems(3) prems)+
     apply (erule impE, assumption)
     apply (drule conjunct2)
     apply assumption
    apply (rule fun_cong[of "PUmap'_ff0 _ _"])
    apply (rule PUmap'_ff0_alpha)
    apply assumption
    done

  apply (rule conjI)
  apply (rule ext)
  apply (erule allE)+
  apply (erule impE, rule assms(1))
  apply (erule impE, rule assms(2))
  apply (erule impE, rule assms)+
   apply (drule conjunct1)
   apply assumption
  apply (erule allE)+
  apply (erule impE, rule assms(1))
  apply (erule impE, rule assms(2))
  apply (erule impE, rule assms)+
  apply (drule conjunct2)
  apply assumption
  done

corollary f_alpha: "suitable_ff0 pick \<Longrightarrow> suitable_ff0 pick' \<Longrightarrow> alpha_\<tau> t t' \<Longrightarrow> f_ff0 pick t = f_ff0 pick' t'"
  apply (rule f_swap_alpha[THEN conjunct2])
       apply assumption+
     apply (rule bij_id)
    apply (rule supp_id_bound)
  unfolding imsupp_id
   apply (rule Int_empty_left)
  apply assumption
  done

lemma exists_suitable_ff0: "\<exists>pick. suitable_ff0 pick"
  unfolding suitable_ff0_def
  apply (rule choice allI)+
  apply (rule exists_suitable_aux)
   apply (rule infinite_var_\<tau>_pre)
  apply (rule \<tau>_pre.Un_bound)
   apply (rule \<tau>_pre.set_bd_UNIV)
  apply (rule card_of_minus_bound)
  apply (rule \<tau>_pre.Un_bound)
   apply (rule \<tau>_pre.Un_bound)
    apply (rule \<tau>.card_of_FVars_bounds)
   apply (rule ff0.small_PFVars)
  apply (rule ff0.small_avoiding_sets)
  done

lemma suitable_ff0_pick0_ff0: "suitable_ff0 pick0_ff0"
  unfolding pick0_ff0_def by (rule someI_ex[OF exists_suitable_ff0])

lemma f0_ff0_alpha: "alpha_\<tau> t t' \<Longrightarrow> f0_ff0 t = f0_ff0 t'"
  by (rule f_alpha[OF suitable_ff0_pick0_ff0 suitable_ff0_pick0_ff0, unfolded f0_ff0_def[symmetric]])

lemmas f0_UFVars'_ff0 = f_UFVars'_ff0[OF suitable_ff0_pick0_ff0, unfolded f0_ff0_def[symmetric]]

lemma f0_low_level_simp: "f0_ff0 (raw_\<tau>_ctor x) p = CTOR_ff0 (map_\<tau>_pre id (pick0_ff0 x p) (\<lambda>t. (rename_\<tau> (pick0_ff0 x p) t, f0_ff0 (rename_\<tau> (pick0_ff0 x p) t))) (\<lambda>t. (t, f0_ff0 t)) x) p"
  unfolding f0_ff0_def f_ff0_simp[OF suitable_ff0_pick0_ff0] \<tau>_pre.map_comp[OF supp_id_bound pick_prems[OF suitable_ff0_pick0_ff0] id_prems] id_o o_id
  unfolding comp_def
  apply (rule refl)
  done

lemma f0_ctor:
  assumes "set2_\<tau>_pre x \<inter> (PFVars_ff0 p \<union> avoiding_set_ff0) = {}" "noclash_ff0 x"
  shows "f0_ff0 (raw_\<tau>_ctor x) p = CTOR_ff0 (map_\<tau>_pre id id (\<lambda>t. (t, f0_ff0 t)) (\<lambda>t. (t, f0_ff0 t)) x) p"
proof -
  have suitable_ff0_pick1: "suitable_ff0 (\<lambda>x' p'. if (x', p') = (x, p) then id else pick0_ff0 x' p')"
unfolding suitable_ff0_def
    apply (rule allI)+
     apply (rule allE[OF suitable_ff0_pick0_ff0[unfolded suitable_ff0_def]])
    apply (erule allE conjE)+
    apply (rule conjI)
    apply (rule bij_if)
     apply assumption
    apply (rule conjI)
     apply (rule supp_if)
     apply assumption
    apply (rule conjI)
     apply (rule imsupp_if_empty)
     apply assumption
    apply (rule image_if_empty)
     apply assumption
    unfolding prod.inject
    apply (erule conjE)
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule trans)
    unfolding Un_assoc
     apply (rule Int_Un_distrib)
    unfolding Un_empty \<tau>.FVars_ctors
    apply (rule conjI)
     apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
     apply (insert assms(2)[unfolded noclash_ff0_def Int_Un_distrib Un_empty])
    apply (erule conjE)+
     apply (rule conjI)+
       apply (assumption | rule Diff_disjoint assms(1))+
    done

  show ?thesis
    apply (rule trans)
   apply (rule fun_cong[of "f0_ff0 _"])
   apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms f0_ff0_def}) 1\<close>)
     apply (rule f_alpha[OF suitable_ff0_pick0_ff0 suitable_ff0_pick1])
     apply (rule \<tau>.alpha_refls)
    apply (rule trans)
    apply (rule f_ff0_simp[OF suitable_ff0_pick1])
    unfolding if_P[OF refl] \<tau>.rename_id0s \<tau>_pre.map_id
    apply (rule arg_cong2[OF _ refl, of _ _ CTOR_ff0])
    apply (rule \<tau>_pre.map_cong)
              apply (rule bij_id supp_id_bound refl)+
    unfolding f0_ff0_def
     apply (rule iffD2[OF prod.inject], rule conjI[OF refl], rule f_alpha[OF suitable_ff0_pick1 suitable_ff0_pick0_ff0], rule \<tau>.alpha_refls)+
    done
qed

lemma f0_swap: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> imsupp u \<inter> avoiding_set_ff0 = {}
  \<Longrightarrow> f0_ff0 (rename_\<tau> u t) p = Umap'_ff0 u t (f0_ff0 t (Pmap_ff0 (inv u) p))"
  unfolding f0_ff0_def
  apply (rule fun_cong[OF f_swap_alpha[OF suitable_ff0_pick0_ff0 suitable_ff0_pick0_ff0 _ _ _ \<tau>.alpha_refls, THEN conjunct1, unfolded PUmap'_ff0_def]])
    apply assumption+
  done

lemma nnoclash_noclash: "nnoclash_ff0 x \<longleftrightarrow> noclash_ff0 (map_\<tau>_pre id id (quot_type.rep Rep_\<tau>) (quot_type.rep Rep_\<tau>) x)"
  unfolding noclash_ff0_def nnoclash_ff0_def \<tau>_pre.set_map[OF id_prems] image_id image_comp comp_def[of FVars_\<tau>] FFVars_\<tau>_def[symmetric]
  apply (rule refl)
  done

(* FINAL RESULT !!! *)
theorem ff0_cctor: "set2_\<tau>_pre x \<inter> (PFVars_ff0 p \<union> avoiding_set_ff0) = {} \<Longrightarrow> nnoclash_ff0 x \<Longrightarrow>
  ff0_ff0 (\<tau>_ctor x) p = Uctor_ff0 (map_\<tau>_pre id id (\<lambda>t. (t, ff0_ff0 t)) (\<lambda>t. (t, ff0_ff0 t)) x) p"
  unfolding \<tau>_pre.set_map(2)[OF id_prems, of "quot_type.rep Rep_\<tau>" "quot_type.rep Rep_\<tau>" x, unfolded image_id, symmetric]
    ff0_ff0_def \<tau>_ctor_def
  apply (rule trans)
   apply (rule fun_cong[OF f0_ff0_alpha])
   apply (rule \<tau>.TT_Quotient_rep_abss)
  apply (rule trans)
   apply (rule f0_ctor)
    apply assumption
   apply (rule iffD1[OF nnoclash_noclash])
   apply assumption
  unfolding CTOR_ff0_def \<tau>_pre.map_comp[OF id_prems id_prems] id_o o_id
  unfolding comp_def map_prod_def prod.case \<tau>.TT_Quotient_abs_reps id_def
  apply (rule refl)
  done

theorem ff0_swap: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> imsupp u \<inter> avoiding_set_ff0 = {}
  \<Longrightarrow> ff0_ff0 (rrename_\<tau> u t) p = Umap_ff0 u t (ff0_ff0 t (Pmap_ff0 (inv u) p))"
  unfolding ff0_ff0_def rrename_\<tau>_def
  apply (rule trans)
   apply (rule fun_cong[OF f0_ff0_alpha])
   apply (rule \<tau>.TT_Quotient_rep_abss)
  apply (rule trans)
   apply (rule f0_swap)
     apply assumption+
  unfolding Umap'_ff0_def \<tau>.TT_Quotient_abs_reps
  apply (rule refl)
  done

theorem ff0_FFVars: "UFVars_ff0 t (ff0_ff0 t p) \<subseteq> FFVars_\<tau> t \<union> PFVars_ff0 p \<union> avoiding_set_ff0"
  unfolding ff0_ff0_def FFVars_\<tau>_def
  apply (rule f0_UFVars'_ff0[of "quot_type.rep Rep_\<tau> t", unfolded UFVars'_ff0_def \<tau>.TT_Quotient_abs_reps])
  done

(* Variable for variable substitution *)

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
  unfolding Uctor_ff0_def CCTOR_def \<tau>_pre.map_comp[OF id_prems assms(1) bij_id supp_id_bound] id_o o_id ssfun_rep_eq[OF assms(1)]
  unfolding comp_def snd_conv avoiding_set_ff0_def Un_empty_right PFVars_ff0_def PFVars_def ssfun_rep_eq[OF assms(1)]
    apply assumption+
  apply (rule refl)
  done

lemma FFVars_vvsubst_weak:
  assumes "|supp (f::'a::var_\<tau>_pre \<Rightarrow> 'a)| <o |UNIV::'a set|"
  shows "FFVars_\<tau> (vvsubst f t) \<subseteq> FFVars_\<tau> t \<union> imsupp f"
  unfolding vvsubst_def
  by (rule ff0_FFVars[of _ "Abs_ssfun f", unfolded avoiding_set_ff0_def Un_empty_right UFVars_ff0_def PFVars_ff0_def PFVars_def ssfun_rep_eq[OF assms(1)]])

end
