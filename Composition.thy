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
  by (rule cinfinite_imp_infinite[OF \<tau>_pre.UNIV_cinfinite])

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

lemmas id_prems = supp_id_bound bij_id supp_id_bound

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

lemmas f0_UFVars'_ff0 = f_UFVars'[OF suitable_ff0_pick0_ff0, unfolded f0_ff0_def[symmetric]]

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
     apply (raw_tactic \<open>SELECT_GOAL (Ctr_Sugar_Tactics.unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
     apply (insert assms(2)[unfolded noclash_ff0_def Int_Un_distrib Un_empty])
    apply (erule conjE)+
     apply (rule conjI)+
       apply (assumption | rule Diff_disjoint assms(1))+
    done

  show ?thesis
    apply (rule trans)
   apply (rule fun_cong[of "f0_ff0 _"])
   apply (raw_tactic \<open>SELECT_GOAL (Ctr_Sugar_Tactics.unfold_thms_tac @{context} @{thms f0_ff0_def}) 1\<close>)
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
  apply (rule f_swap_alpha[OF suitable_ff0_pick0_ff0 suitable_ff0_pick0_ff0 _ _ _ \<tau>.alpha_refls, THEN conjunct1, unfolded PUmap'_ff0_def])
    apply assumption+
  done

lemma nnoclash_noclash: "nnoclash_ff0 x \<longleftrightarrow> noclash_ff0 (map_\<tau>_pre id id (quot_type.rep Rep_\<tau>) (quot_type.rep Rep_\<tau>) x)"
  unfolding noclash_ff0_def nnoclash_ff0_def \<tau>_pre.set_map[OF id_prems] image_id image_comp comp_def[of FVars_\<tau>] FFVars_\<tau>_def[symmetric]
  apply (rule refl)
  done

(* FINAL RESULT !!! *)
theorem ff0_cctor': "set2_\<tau>_pre x \<inter> (PFVars_ff0 p \<union> avoiding_set_ff0) = {} \<Longrightarrow> nnoclash_ff0 x \<Longrightarrow>
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

theorem ff0_cctor: "set2_\<tau>_pre x \<inter> (PFVars p \<union> {}) = {} \<Longrightarrow> nnoclash_ff0 x \<Longrightarrow>
  ff0_ff0 (\<tau>_ctor x) p = CCTOR (map_\<tau>_pre id id (\<lambda>t. (t, ff0_ff0 t)) (\<lambda>t. (t, ff0_ff0 t)) x) p"
  by (rule ff0_cctor'[unfolded Uctor_ff0_def PFVars_ff0_def avoiding_set_ff0_def])

theorem ff0_swap': "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> imsupp u \<inter> avoiding_set_ff0 = {}
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

theorem ff0_swap: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> imsupp u \<inter> {} = {}
  \<Longrightarrow> ff0_ff0 (rrename_\<tau> u t) p = rrename_\<tau> u (ff0_ff0 t (compSS (inv u) p))"
  by (rule ff0_swap'[unfolded Pmap_ff0_def Umap_ff0_def avoiding_set_ff0_def])

theorem ff0_FFVars': "UFVars_ff0 t (ff0_ff0 t p) \<subseteq> FFVars_\<tau> t \<union> PFVars_ff0 p \<union> avoiding_set_ff0"
  unfolding ff0_ff0_def FFVars_\<tau>_def
  apply (rule f0_UFVars'_ff0[of "quot_type.rep Rep_\<tau> t", unfolded UFVars'_ff0_def \<tau>.TT_Quotient_abs_reps])
  done

theorem ff0_FFVars: "FFVars_\<tau> (ff0_ff0 t p) \<subseteq> FFVars_\<tau> t \<union> PFVars p \<union> {}"
  by (rule ff0_FFVars'[unfolded UFVars_ff0_def PFVars_ff0_def avoiding_set_ff0_def])

hide_fact Uctor_ff0_def PFVars_ff0_def avoiding_set_ff0_def UFVars_ff0_def Umap_ff0_def Pmap_ff0_def

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
  unfolding CCTOR_def \<tau>_pre.map_comp[OF id_prems assms(1) bij_id supp_id_bound] id_o o_id ssfun_rep_eq[OF assms(1)]
  unfolding comp_def snd_conv Un_empty_right PFVars_def ssfun_rep_eq[OF assms(1)]
    apply assumption+
  apply (rule refl)
  done

lemma FFVars_vvsubst_weak:
  assumes "|supp (f::'a::var_\<tau>_pre \<Rightarrow> 'a)| <o |UNIV::'a set|"
  shows "FFVars_\<tau> (vvsubst f t) \<subseteq> FFVars_\<tau> t \<union> imsupp f"
  unfolding vvsubst_def
  by (rule ff0_FFVars[of _ "Abs_ssfun f", unfolded Un_empty_right PFVars_def ssfun_rep_eq[OF assms(1)]])

end
