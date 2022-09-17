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

ML_file \<open>./Tools/mrbnf_vvsubst_tactics.ML\<close>
ML_file \<open>./Tools/mrbnf_vvsubst.ML\<close>

local_setup \<open>fn lthy =>
let
  val (x, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint I
    (the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Composition.\<tau>")) lthy
in lthy end\<close>

lemma infinite_var_\<tau>_pre: "infinite (UNIV :: 'a::var_\<tau>_pre set)"
  by (rule cinfinite_imp_infinite[OF \<tau>_pre.UNIV_cinfinite])

(******************** Definitions for variable-for-variable substitution ***********)

lemma UFVars_subset: "set2_\<tau>_pre y \<inter> (PFVars p \<union> {}) = {} \<Longrightarrow>
       (\<And>t pu p. (t, pu) \<in> set3_\<tau>_pre y \<union> set4_\<tau>_pre y \<Longrightarrow> FFVars_\<tau> (pu p) \<subseteq> FFVars_\<tau> t \<union> PFVars p \<union> {}) \<Longrightarrow>
       FFVars_\<tau> (CCTOR y p) \<subseteq> FFVars_\<tau> (\<tau>_ctor (map_\<tau>_pre id id fst fst y)) \<union> PFVars p \<union> {}"
  unfolding Un_empty_right CCTOR_def PFVars_def \<tau>.FFVars_cctors
    \<tau>_pre.set_map[OF supp_id_bound bij_id supp_id_bound] image_id
    \<tau>_pre.set_map[OF iffD1[OF mem_Collect_eq Rep_ssfun_\<tau>] bij_id supp_id_bound] image_comp comp_def
  apply (rule Un_mono')+
    apply (rule iffD1[OF arg_cong2[OF refl Un_commute, of "(\<subseteq>)"] image_imsupp_subset])
   apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
    apply (rule Diff_Un_disjunct)
    apply assumption
   apply (rule Diff_mono[OF _ subset_refl])
   apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
    apply (rule UN_extend_simps(2))
   apply (rule bool.exhaust[of "set3_\<tau>_pre y = {}", unfolded eq_True eq_False])
  unfolding if_P if_not_P UN_empty'
    apply (rule empty_subsetI)
   apply (rule UN_mono[OF subset_refl])
  subgoal for x
    apply (rule prod.exhaust[of x])
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    unfolding fst_conv snd_conv
    apply (drule UnI1)
    apply assumption
    done
  apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
   apply (rule UN_extend_simps(2))
  apply (rule bool.exhaust[of "set4_\<tau>_pre y = {}", unfolded eq_True eq_False])
  unfolding if_P if_not_P UN_empty'
   apply (rule empty_subsetI)
  apply (rule UN_mono[OF subset_refl])
  subgoal for x
    apply (rule prod.exhaust[of x])
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    unfolding fst_conv snd_conv
    apply (drule UnI2)
    apply assumption
    done
  done

lemma Umap_Uctor: "bij (f::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow>
       |supp f| <o |UNIV::'a set| \<Longrightarrow>
       rrename_\<tau> f (CCTOR y p) =
       CCTOR (map_\<tau>_pre f f (\<lambda>(t, pu). (rrename_\<tau> f t, \<lambda>p. rrename_\<tau> f (pu (compSS (inv f) p)))) (\<lambda>(t, pu). (rrename_\<tau> f t, \<lambda>p. rrename_\<tau> f (pu (compSS (inv f) p)))) y) (compSS f p)"
  unfolding CCTOR_def \<tau>_pre.map_comp[OF iffD1[OF mem_Collect_eq Rep_ssfun_\<tau>] bij_id supp_id_bound] id_o o_id \<tau>.rrename_cctors
    \<tau>_pre.map_comp[OF _ _ _ iffD1[OF mem_Collect_eq Rep_ssfun_\<tau>] bij_id supp_id_bound]
  unfolding comp_def case_prod_beta snd_conv compSS_rep_eq inv_simp1
    fun_cong[OF compSS_comp[OF bij_imp_bij_inv supp_inv_bound], unfolded comp_def, symmetric] id_def[symmetric] compSS_id
  unfolding id_def
  apply (rule refl)
  done

(***************************************************************************************)

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
    PFVars_Pmaps = [fn ctxt => EVERY1 [rtac ctxt @{thm PFVars_Pmap}, REPEAT_DETERM o assume_tac ctxt]],
    small_PFVarss = [fn ctxt => rtac ctxt @{thm small_PFVars} 1]
  };
  val model = {
    U = @{typ "'a::var_\<tau>_pre \<tau>"},
    fp_result = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Composition.\<tau>"),
    UFVars = [@{term "\<lambda>(_::'a::var_\<tau>_pre \<tau>) (x::'a::var_\<tau>_pre \<tau>). FFVars_\<tau> x"}],
    Umap = @{term "\<lambda>f (_::'a::var_\<tau>_pre \<tau>) (x::'a::var_\<tau>_pre \<tau>). rrename_\<tau> f x"},
    Uctor = @{term CCTOR},
    avoiding_sets = [@{term "{}::'a::var_\<tau>_pre set"}],
    parameters = {
      P = @{typ "'a::var_\<tau>_pre ssfun_\<tau>"},
      PFVarss = [@{term "PFVars"}],
      Pmap = @{term "compSS:: ('a::var_\<tau>_pre \<Rightarrow> 'a) \<Rightarrow> _ \<Rightarrow> _"},
      axioms = parameter_tacs
    },
    axioms = model_tacs
  };
  val (res, lthy) = MRBNF_Recursor.create_binding_recursor I model @{binding ff0} lthy
  val notes =
    [("ff0_cctor", [#rec_Uctor res]),
     ("ff0_swap", [#rec_swap res]),
     ("ff0_UFVars", #rec_UFVarss res)
    ] |> (map (fn (thmN, thms) =>
      ((Binding.name thmN, []), [(thms, [])])
    ));
  val (_, lthy) = Local_Theory.notes notes lthy
in lthy end
\<close>

thm ff0_cctor ff0_swap ff0_UFVars

(************************************************************************************)

lemmas id_prems = supp_id_bound bij_id supp_id_bound

definition vvsubst where "vvsubst f x \<equiv> ff0 x (Abs_ssfun_\<tau> f)"

lemma vvsubst_cctor:
  assumes "|supp (f::'a::var_\<tau>_pre \<Rightarrow> 'a)| <o |UNIV::'a set|"
  shows "set2_\<tau>_pre x \<inter> imsupp f = {} \<Longrightarrow> noclash_\<tau> x \<Longrightarrow>
  vvsubst f (\<tau>_ctor x) = \<tau>_ctor (map_\<tau>_pre f id (vvsubst f) (vvsubst f) x)"
  unfolding vvsubst_def
  apply (rule trans)
   apply (rule ff0_cctor)
  unfolding CCTOR_def \<tau>_pre.map_comp[OF id_prems assms(1) bij_id supp_id_bound] id_o o_id ssfun_\<tau>_rep_eq[OF assms(1)]
  unfolding comp_def snd_conv Un_empty_right PFVars_def ssfun_\<tau>_rep_eq[OF assms(1)]
    apply assumption+
  apply (rule refl)
  done

lemma FFVars_vvsubst_weak:
  assumes "|supp (f::'a::var_\<tau>_pre \<Rightarrow> 'a)| <o |UNIV::'a set|"
  shows "FFVars_\<tau> (vvsubst f t) \<subseteq> FFVars_\<tau> t \<union> imsupp f"
  unfolding vvsubst_def
  by (rule ff0_UFVars[of _ "Abs_ssfun_\<tau> f", unfolded Un_empty_right PFVars_def ssfun_\<tau>_rep_eq[OF assms(1)]])

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
  unfolding noclash_\<tau>_def Int_Un_distrib Un_empty
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
  K (Ctr_Sugar_Tactics.unfold_thms_tac ctxt @{thms noclash_\<tau>_def Int_Un_distrib Un_empty}),
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
  unfolding \<tau>_pre.set_map[OF assms(1) bij_id supp_id_bound] image_id noclash_\<tau>_def
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
