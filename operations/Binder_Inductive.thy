theory Binder_Inductive
  imports "Untyped_Lambda_Calculus.LC"
begin

declare [[inductive_internals]]
inductive step :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "step (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)"
| AppL: "step e1 e1' \<Longrightarrow> step (App e1 e2) (App e1' e2)"
| AppR: "step e2 e2' \<Longrightarrow> step (App e1 e2) (App e1 e2')"
| Xi: "step e e' \<Longrightarrow> step (Lam x e) (Lam x e')"
print_theorems

(* user goals *)
lemma perm_id0s:
  "rrename id = id"
  "rrename id = id"
  by (rule term.permute_id0)+

lemma perm_comps:
  fixes \<sigma> :: "var \<Rightarrow> var"
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|" "bij \<sigma>'" "|supp \<sigma>'| <o |UNIV::var set|"
  shows
    "rrename \<sigma> (rrename \<sigma>' x1) = rrename (\<sigma> \<circ> \<sigma>') x1"
    "rrename \<sigma> (rrename \<sigma>' x2) = rrename (\<sigma> \<circ> \<sigma>') x2"
  by (rule term.permute_comp assms)+

lemma perm_supports:
  fixes \<sigma> :: "var \<Rightarrow> var"
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
  shows
    "(\<And>a. a \<in> FFVars x1 \<Longrightarrow> \<sigma> a = a) \<Longrightarrow> rrename \<sigma> x1 = x1"
    "(\<And>a. a \<in> FFVars x2 \<Longrightarrow> \<sigma> a = a) \<Longrightarrow> rrename \<sigma> x2 = x2"
  by (rule term.permute_cong_id[OF assms], assumption)+

lemma supp_smalls:
  fixes x1 x2::"trm"
  shows
    "|FFVars x1| <o |UNIV::var set|"
    "|FFVars x2| <o |UNIV::var set|"
  by (rule term.set_bd_UNIV)+

lemma supp_seminat:
  fixes \<sigma> :: "var \<Rightarrow> var"
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
  shows
    "FFVars (rrename \<sigma> x1) \<subseteq> \<sigma> ` FFVars x1"
    "FFVars (rrename \<sigma> x2) \<subseteq> \<sigma> ` FFVars x2"
  using term.FVars_permute assms by blast+

text \<open>This is automatically derived from @{thm step_def} and the binder annotations\<close>
thm step_def
definition "G \<equiv> \<lambda>p (B::var set) x1 x2.
  (\<exists>x e1 e2. B = {x} \<and> x1 = App (Lam x e1) e2 \<and> x2 = tvsubst (Var(x := e2)) e1) \<or>
  (\<exists>e1 e1' e2. B = {} \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p e1 e1') \<or>
  (\<exists>e2 e2' e1. B = {} \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p e2 e2') \<or>
  (\<exists>e e' x. B = {x} \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p e e')"

lemma G_equiv:
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
  shows "G R B x1 x2 \<Longrightarrow> G (\<lambda>x1 x2. R (rrename (inv \<sigma>) x1) (rrename (inv \<sigma>) x2)) (\<sigma> ` B) (rrename \<sigma> x1) (rrename \<sigma> x2)"
  using assms apply -
  unfolding G_def
  by (elim disj_forward) (auto simp: term.permute_comp rrename_tvsubst_comp)

abbreviation "supp_T x1 x2 \<equiv> FFVars x1 \<union> FFVars x2"

lemma fresh: "\<exists>xx. xx \<notin> supp_T (x1::trm) x2"
  using Lam_avoid supp_smalls(2) term.set(2) by blast

lemma G_refresh:
  assumes
    "\<And>x1 x2. R x1 x2 \<Longrightarrow> step x1 x2"
    "\<And>\<sigma> x1 x2. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> R x1 x2 \<Longrightarrow> R (rrename \<sigma> x1) (rrename \<sigma> x2)"
  shows "G R B x1 x2 \<Longrightarrow> \<exists>B'. B' \<inter> supp_T x1 x2 = {} \<and> G R B' x1 x2"
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib G_def
    apply (elim disj_forward exE)
       apply auto
    using fresh[of x1 x2] assms(2) Lam_refresh apply auto
    by (metis Lam_eq_tvsubst singletonD)

lemma infinite_UNIV: "infinite (UNIV::var set)"
  by (rule infinite_var)

lemma B_small: "G R B x1 x2 \<Longrightarrow> |B| <o |UNIV::var set|"
  unfolding G_def by (auto simp: singl_bound emp_bound)

(****** BEGIN AUTOMATION *******)
lemmas perm_ids = perm_id0s[THEN fun_cong, THEN trans[OF _ id_apply]]

lemma G_mono: "mono G"
  apply (unfold G_def)
  apply (rule monoI)
  apply (rule le_funI le_boolI')+
  apply (assumption
      | tactic \<open>resolve_tac @{context} (Inductive.get_monos @{context}) 1\<close>
      | erule le_funE
      | drule le_boolD
  )+
  done

lemmas G_mono' = monoD[THEN le_funD, THEN le_funD, THEN le_funD, OF G_mono, THEN le_boolD, THEN mp, rotated]

lemma G_mmono: "mono (\<lambda>p x1 x2. \<exists>B. G p B x1 x2)"
  apply (rule monoI)
  apply (rule le_funI le_boolI')+
  apply (rule ex_mono)
  apply (rule impI)
  apply (erule G_mono')
  apply assumption
  done

definition "II \<equiv> lfp (\<lambda>p x1 x2. \<exists>B. G p B x1 x2)"

lemmas II_induct = lfp_induct[THEN le_funD, THEN le_funD, OF G_mmono, THEN le_boolD, THEN mp, rotated]

lemma II_eq: "II = step"
  apply (unfold II_def step_def)
  apply (rule ext)+
  apply (rule iffI)

   apply (erule II_induct)
   apply (rule le_funI)+
   apply (rule le_boolI)
   apply (unfold inf_apply inf_bool_def)
   apply (erule exE)+
   apply (drule G_mono')
    apply (rule le_funI)+
    apply (rule le_boolI)
    apply (erule conjunct2)
   apply (unfold G_def)[1]
   apply (subst lfp_unfold[OF step.mono])
    (* REPEAT_DETERM *)
   apply (erule disj_forward)?
    apply (erule exE)+
    apply (erule conjE)
    apply (rule exI)+
    apply assumption
    (* repeated *)
   apply (erule disj_forward)?
    apply (erule exE)+
    apply (erule conjE)
    apply (rule exI)+
    apply assumption
    (* repeated *)
   apply (erule disj_forward)?
    apply (erule exE)+
    apply (erule conjE)
    apply (rule exI)+
    apply assumption
    (* repeated *)
   apply (erule disj_forward)?
   apply (erule exE)+
   apply (erule conjE)
   apply (rule exI)+
   apply assumption
    (* END REPEAT_DETERM *)

  apply (erule lfp_induct[THEN le_funD, THEN le_funD, OF step.mono, THEN le_boolD, THEN mp, rotated])
  apply (rule le_funI)+
  apply (rule le_boolI)
  apply (unfold inf_apply inf_bool_def)
  apply (drule monoD[OF step.mono, THEN le_funD, THEN le_funD, THEN le_boolD, THEN mp, rotated])
   apply (rule le_funI)+
   apply (rule le_boolI)
   apply (erule conjunct2)
  apply (subst lfp_unfold[OF G_mmono])
  apply (unfold G_def ex_disj_distrib)
    (* REPEAT_DETERM *)
  apply (erule disj_forward)?
   apply (erule exE)+
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply assumption
    (* repeated *)
  apply (erule disj_forward)?
   apply (erule exE)+
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply assumption
    (* repeated *)
  apply (erule disj_forward)?
   apply (erule exE)+
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply assumption
    (* repeated *)
  apply (erule disj_forward)?
  apply (erule exE)+
  apply (rule exI)+
  apply (rule conjI)
   apply (rule refl)
  apply assumption
    (* END REPEAT_DETERM *)
  done

lemma II_equiv:
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
  shows "II x1 x2 \<Longrightarrow> II (rrename \<sigma> x1) (rrename \<sigma> x2)"
  apply (unfold II_def)
  apply (erule II_induct)
  apply (rule le_funI)+
  apply (rule le_boolI)
  apply (erule exE)+
  apply (drule G_mono')
   apply (rule le_funI)+
   apply (rule le_boolI)
   apply (unfold inf_apply inf_bool_def)[1]
   apply (erule conjunct2)
  apply (drule G_equiv[OF assms])
  apply (subst (asm) inv_o_simp2 perm_comps, (rule bij_imp_bij_inv supp_inv_bound assms)+)+
  apply (unfold perm_ids)
  apply (subst lfp_unfold[OF G_mmono])
  apply (rule exI)
  apply assumption
  done

lemma G_mmono': "mono (\<lambda>p x1 x2. \<exists>B. B \<inter> supp_T x1 x2 = {} \<and> G p B x1 x2)"
  apply (rule monoI)
  apply (rule le_funI le_boolI')+
  apply (rule ex_mono)
  apply (rule impI)
  apply (erule conjE)
  apply (erule conjI)
  apply (erule G_mono')
  apply assumption
  done

definition "II' \<equiv> lfp (\<lambda>p x1 x2. \<exists>B. B \<inter> supp_T x1 x2 = {} \<and> G p B x1 x2)"
lemmas II'_induct = lfp_induct[THEN le_funD, THEN le_funD, OF G_mmono', THEN le_boolD, THEN mp, rotated]

lemma II'_imp_II: "II' x1 x2 \<Longrightarrow> II x1 x2"
  apply (unfold II'_def II_def)
  apply (erule II'_induct)
  apply (rule le_funI le_boolI)+
  apply (drule ex_conjunct2)
  apply (erule exE)+
  apply (drule G_mono')
   apply (rule le_funI)+
   apply (unfold inf_apply inf_bool_def)
   apply (rule le_boolI)
   apply (erule conjunct2)
  apply (subst lfp_unfold[OF G_mmono])
  apply (rule exI)
  apply assumption
  done

lemma supp_int_equiv:
  fixes B::"var set"
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
  shows "B \<inter> supp_T x1 x2 = {} \<Longrightarrow> \<sigma> ` B \<inter> supp_T (rrename \<sigma> x1) (rrename \<sigma> x2) = {}"
  apply (rule Int_subset_empty2)
   apply (rule trans)
    apply (rule image_Int[symmetric])
    apply (rule bij_is_inj)
    apply (rule assms)
   apply (rule iffD2[OF image_is_empty])
   apply assumption
  apply (unfold image_Un)
  apply (rule Un_mono)+
   apply (rule supp_seminat[OF assms])+
  done

lemma II'_equiv:
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
  shows "II' x1 x2 \<Longrightarrow> II' (rrename \<sigma> x1) (rrename \<sigma> x2)"
  apply (unfold II'_def)
  apply (erule II'_induct)
  apply (rule le_funI)+
  apply (rule le_boolI)
  apply (unfold inf_apply inf_bool_def)
  apply (erule exE)+
  apply (erule conjE)
  apply (drule G_mono')
   apply (rule le_funI)+
   apply (rule le_boolI)
   apply (erule conjunct2)
  apply (drule G_equiv[OF assms])
  apply (subst (asm) inv_o_simp2 perm_comps, (rule bij_imp_bij_inv supp_inv_bound assms)+)+
  apply (unfold perm_ids)
  apply (subst lfp_unfold[OF G_mmono'])
  apply (rule exI)
  apply (rule conjI[rotated])
   apply assumption
  apply (erule supp_int_equiv[OF assms])
  done

lemma II_eq_II': "II = II'"
  apply (rule ext)+
  apply (rule iffI[rotated])
   apply (erule II'_imp_II)
  apply (unfold II_def)
  apply (erule II_induct)
  apply (rule le_funI)+
  apply (rule le_boolI)
  apply (erule exE)+
  apply (drule G_mono')
   apply (rule le_funI)+
   apply (rule le_boolI)
   apply (unfold inf_apply inf_bool_def)
   apply (erule conjunct2)
  apply (drule G_refresh[unfolded II_eq[symmetric], rotated -1])
    apply (erule II'_imp_II)
   apply (erule II'_equiv[rotated -1])
    apply assumption+
  apply (erule exE)
  apply (subst II'_def)
  apply (erule conjE)
  apply (subst lfp_unfold[OF G_mmono'])
  apply (rule exI)
  apply (erule conjI)
  apply (unfold II'_def)
  apply assumption
  done

lemmas Un_bound = card_of_Un_ordLess_infinite[OF infinite_UNIV]

lemma extend_fresh:
  fixes K::"'p \<Rightarrow> var set"
  shows "II x1 x2 \<Longrightarrow> |B| <o |UNIV::var set| \<Longrightarrow> |K p| <o |UNIV::var set| \<Longrightarrow> B \<inter> supp_T x1 x2 = {}
    \<Longrightarrow> \<exists>\<rho>. bij \<rho> \<and> |supp \<rho>| <o |UNIV::var set| \<and> \<rho> ` B \<inter> K p = {} \<and> \<rho> ` B \<inter> supp_T x1 x2 = {}
        \<and> id_on (supp_T x1 x2) \<rho>"
  apply (drule eextend_fresh[rotated -1])
      apply assumption
     defer
     apply (rule infinite_UNIV)
    apply (rule Un_upper2)
   apply (erule exE conjE)+
   apply (rule exI)
   apply (rule conjI, assumption)+
   apply (rule conjI)
    apply (erule Int_subset_empty2)
    apply (rule Un_upper1)
   apply (rule conjI)
    apply (erule Int_subset_empty2)
    apply (rule Un_upper2)
   apply assumption
  apply (rule Un_bound)
   apply assumption
  apply (rule Un_bound supp_smalls)+
  done

ML \<open>
val lthy = @{context}
\<close>

lemma perm_comp_inv_ids:
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
  shows
    "rrename \<sigma> (rrename (inv \<sigma>) x1) = (x1::trm)"
    "rrename \<sigma> (rrename (inv \<sigma>) x2) = (x2::trm)"
   apply (rule trans)
    apply (rule perm_comps)
       apply (rule bij_imp_bij_inv supp_inv_bound assms)+
   apply (subst inv_o_simp2)
    apply (rule assms)
   apply (rule perm_ids)
  (* repeated *)
   apply (rule trans)
    apply (rule perm_comps)
       apply (rule bij_imp_bij_inv supp_inv_bound assms)+
   apply (subst inv_o_simp2)
    apply (rule assms)
   apply (rule perm_ids)
  done

lemma II'_equiv_strong:
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
  shows "II' x1 x2 = II' (rrename \<sigma> x1) (rrename \<sigma> x2)"
  apply (rule iffI)
   apply (erule II'_equiv[OF assms])
  apply (drule II'_equiv[rotated -1])
    prefer 3 (* 2 * vars + 1 *)
    apply (subst (asm) perm_comps)
        prefer 5 (* 4 * vars + 1 *)
        apply (subst (asm) inv_o_simp1)
         apply (rule assms)
        apply (subst (asm) perm_comps inv_o_simp1, (rule bij_imp_bij_inv supp_inv_bound assms)+)+
        apply (unfold perm_ids)
        apply assumption
       apply (rule bij_imp_bij_inv supp_inv_bound assms)+
  done

lemma BE_iinduct_aux:
  fixes K::"'p \<Rightarrow> var set"
  assumes smalls: "\<And>p. |K p| <o |UNIV::var set|"
  and II: "II' x1 x2"
  and step: "\<And>B x1 x2 p. B \<inter> K p = {} \<Longrightarrow> B \<inter> supp_T x1 x2 = {} \<Longrightarrow>
    G (\<lambda>x1' x2'. II' x1' x2' \<and> All (R x1' x2')) B x1 x2 \<Longrightarrow> R x1 x2 p"
shows "\<forall>\<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<longrightarrow> All (R (rrename \<sigma> x1) (rrename \<sigma> x2))"
  apply (rule II'_induct[unfolded II'_def[symmetric], OF II])
  apply (rule le_funI)+
  apply (rule le_boolI)
  apply (erule exE)+
  apply (erule conjE)
  apply (rule allI impI)+
  apply (unfold inf_apply inf_bool_def)
  apply (drule supp_int_equiv[rotated -1])
  apply assumption+
  apply (drule extend_fresh[of _ _ _ K, rotated -1])
     apply (unfold II_eq_II'[symmetric])[1]
     apply (rule II_equiv[rotated -1])
     apply (subst II_def)
     apply (subst lfp_unfold[OF G_mmono])
     apply (rule exI)
     apply (unfold II_def[symmetric])[1]
     apply (erule G_mono')
     apply (rule le_funI)+
     apply (rule le_boolI)
     apply (erule conjE)
       apply assumption+
    apply (rule ordLeq_ordLess_trans)
     apply (rule card_of_image)
    apply (erule B_small)
   apply (rule smalls)
  apply (erule exE conjE)+
  apply (rule step)
    apply assumption
   apply assumption
  apply (unfold image_comp)
  apply (tactic \<open>resolve_tac @{context} [Drule.rotate_prems ~1 (
    iffD2 OF [MRBNF_Util.mk_arg_cong lthy (2 + 2) @{term G} OF (replicate 2 refl)
  ])] 1\<close>)
  apply (rule G_equiv[THEN G_mono'])
       prefer 3
       apply assumption
      apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
    apply (rule le_funI)+
    apply (rule le_boolI)
    apply (erule conjE)
    apply (rule conjI)
     apply (erule iffD2[OF II'_equiv_strong, rotated -1])
      apply (rule bij_imp_bij_inv supp_inv_bound bij_comp supp_comp_bound infinite_UNIV | assumption)+
    apply (rule allI)
    apply (erule allE)
    apply (erule impE)
     prefer 2
     apply (erule impE)
      prefer 2
      apply (subst (asm) perm_comp_inv_ids, (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+)+
      apply (erule allE)
      apply assumption
     apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
(* REPEAT_DETERM *)
   apply (rule sym)
   apply (rule trans)
    apply (rule perm_comps[symmetric])
  apply assumption+
   apply (rule perm_supports)
     apply assumption+
   apply (erule id_onD)
   apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 2 1] 1\<close>)
  (* repeated *)
   apply (rule sym)
   apply (rule trans)
    apply (rule perm_comps[symmetric])
  apply assumption+
   apply (rule perm_supports)
     apply assumption+
   apply (erule id_onD)
   apply (tactic \<open>eresolve_tac @{context} [BNF_Util.mk_UnIN 2 2] 1\<close>)
  (* END REPEAT_DETERM *)
  done

lemma BE_iinduct:
  fixes K::"'p \<Rightarrow> var set"
  assumes smalls: "\<And>p. |K p| <o |UNIV::var set|"
  and II: "step x1 x2"
  and step: "\<And>B x1 x2 p. B \<inter> K p = {} \<Longrightarrow> B \<inter> supp_T x1 x2 = {} \<Longrightarrow>
    G (\<lambda>x1' x2'. step x1' x2' \<and> All (R x1' x2')) B x1 x2 \<Longrightarrow> R x1 x2 p"
shows "R x1 x2 p"
  apply (rule BE_iinduct_aux[of K, unfolded II_eq_II'[symmetric] II_eq, OF smalls II,
    THEN spec, THEN mp[OF _ bij_id, THEN mp[OF _ supp_id_bound]], THEN spec,
    unfolded perm_ids
  ])
  apply (rule step)
  apply assumption+
  done

lemma step_strong_induct[consumes 1, case_names Bound Beta AppL AppR Xi]:
  fixes K::"'p \<Rightarrow> var set"
  assumes consumes: "step x1 x2" "\<And>p. |K p| <o |UNIV::var set|"
  and steps:
"\<And>x e1 e2 p. x \<notin> K p \<Longrightarrow> P (App (Lam x e1) e2) (tvsubst (Var(x := e2)) e1) p"
"\<And>e1 e1' e2 p. step e1 e1' \<Longrightarrow> \<forall>p. P e1 e1' p \<Longrightarrow> P (App e1 e2) (App e1' e2) p"
"\<And>e2 e2' e1 p. step e2 e2' \<Longrightarrow> \<forall>p. P e2 e2' p \<Longrightarrow> P (App e1 e2) (App e1 e2') p"
"\<And>e e' x p. x \<notin> K p \<Longrightarrow> step e e' \<Longrightarrow> \<forall>p. P e e' p \<Longrightarrow> P (Lam x e) (Lam x e') p"
shows "\<forall>p. P x1 x2 p"
  apply (rule allI)
  apply (rule BE_iinduct[of K])
  apply (rule consumes)+
  apply (unfold G_def)
  (* REPEAT_DETERM *)
  apply (erule disjE)?
   apply (erule exE conjE)+
   apply hypsubst
   apply (unfold disjoint_single induct_rulify)?
  subgoal premises prems
   apply (rule steps(1))
    apply (assumption | rule prems (* tryall prems[THEN conjunct1] prems[THEN conjunct2] *))+
    done
  (* repeated *)
  apply (erule disjE)?
   apply (erule exE conjE)+
   apply hypsubst
   apply (unfold disjoint_single induct_rulify)?
  subgoal premises prems
   apply (rule steps(2))
    apply (assumption | rule prems (* tryall prems[THEN conjunct1] prems[THEN conjunct2] *))+
    done
  (* repeated *)
  apply (erule disjE)?
   apply (erule exE conjE)+
   apply hypsubst
   apply (unfold disjoint_single induct_rulify)?
  subgoal premises prems
   apply (rule steps(3))
    apply (assumption | rule prems (* tryall prems[THEN conjunct1] prems[THEN conjunct2] *))+
    done
  (* repeated *)
  apply (erule disjE)?
   apply (erule exE conjE)+
   apply hypsubst
   apply (unfold disjoint_single induct_rulify)?
  subgoal premises prems
   apply (rule steps(4))
    apply (assumption | rule prems (* tryall prems[THEN conjunct1] prems[THEN conjunct2] *))+
    done
  (* END REPEAT_DETERM *)
  done

end