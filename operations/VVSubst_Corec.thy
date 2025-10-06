theory VVSubst_Corec
  imports "./Corecursor"
begin

lemma insert_subset_Collect: "insert x A \<subseteq> Collect P \<longleftrightarrow> P x \<and> A \<subseteq> Collect P"
  by blast

type_synonym 'a U = "'a term \<times> ('a \<Rightarrow> 'a)"

definition Udtor_vvsubst :: "'a U \<Rightarrow> ('a::covar, 'a, 'a term + 'a U, 'a term + 'a U) term_pre set" where
  "Udtor_vvsubst p = (case p of (t, f) \<Rightarrow> { map_term_pre f id (\<lambda>t. Inr (t, f)) (\<lambda>t. Inr (t, f))
    t' | t'. t = term_ctor t' \<and> set2_term_pre t' \<inter> imsupp f = {} }
  )"

definition Var :: "'a::var \<Rightarrow> 'a term" where
  "Var a = term_ctor (Abs_term_pre (Inl a))"
definition App :: "'a::var term \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "App t1 t2 = term_ctor (Abs_term_pre (Inr (Inl (t1, t2))))"
definition Lam :: "'a::var \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "Lam a t = term_ctor (Abs_term_pre (Inr (Inr (a, t))))"

definition SSupp :: "('a \<Rightarrow> 'a::var term) \<Rightarrow> 'a set" where
  "SSupp \<rho> = { a. \<rho> a \<noteq> Var a }"
definition IImsupp :: "('a \<Rightarrow> 'a::var term) \<Rightarrow> 'a set" where
  "IImsupp \<rho> = SSupp \<rho> \<union> (\<Union>a\<in>SSupp \<rho>. FVars_term (\<rho> a))"

type_synonym 'a U' = "'a term \<times> ('a \<Rightarrow> 'a term)"
definition Udtor_tvsubst :: "'a::covar U' \<Rightarrow> ('a::covar, 'a, 'a term + 'a U', 'a term + 'a U') term_pre set" where
  "Udtor_tvsubst p = (case p of (t, \<rho>) \<Rightarrow> if (\<exists>a. t = Var a) then
    { map_term_pre id id Inl Inl t' | t'. \<rho> (SOME a. t' = Abs_term_pre (Inl a)) = term_ctor t' }
  else { map_term_pre id id (\<lambda>t. Inr (t, \<rho>)) (\<lambda>t. Inr (t, \<rho>))
    t' | t'. t = term_ctor t' \<and> set2_term_pre t' \<inter> IImsupp \<rho> = {} }
  )"

definition Umap_vvsubst :: "('a::covar \<Rightarrow> 'a) \<Rightarrow> 'a U \<Rightarrow> 'a U" where
  "Umap_vvsubst g p = (case p of (t, f) \<Rightarrow>
    (permute_term g t, compSS g f)
  )"

definition UFVars_vvsubst :: "'a U \<Rightarrow> 'a::covar set" where
  "UFVars_vvsubst p = (case p of (t, f) \<Rightarrow> FVars_term t \<union> imsupp f)"

definition valid_U_vvsubst :: "'a U \<Rightarrow> bool" where
  "valid_U_vvsubst p = (case p of (t, f) \<Rightarrow> |supp f| <o |UNIV::'a set| )"

interpretation vvsubst: COREC Udtor_vvsubst Umap_vvsubst UFVars_vvsubst valid_U_vvsubst
  apply (unfold_locales)
         apply (unfold Udtor_vvsubst_def Umap_vvsubst_def UFVars_vvsubst_def valid_U_vvsubst_def case_prod_beta snd_conv fst_conv)

  subgoal for d
    apply (rule fresh_cases[of "imsupp (snd d)" "fst d"])
     apply (rule iffD2[OF imsupp_supp_bound])
      apply (rule infinite_UNIV)
    apply assumption
    apply (unfold Collect_empty_eq not_all not_not)
    apply (rule exI)+
    apply (rule conjI[rotated])+
      apply assumption+
    apply (rule refl)
    done

  subgoal for X X' d
    apply (unfold insert_subset_Collect)
    apply (erule conjE)+
    apply (rotate_tac -1)
    apply (erule thin_rl)
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (subst term_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
    apply (unfold image_comp[unfolded comp_def] image_id sum.case fst_conv snd_conv)

    apply (drule TT_inject0s[THEN iffD1, OF trans, OF sym])
     apply assumption
    apply (erule exE conjE)+
    apply (rule exI)+
    apply (rule conjI, assumption)+
    apply (rule conjI)
     apply (erule id_on_antimono)
     apply (rule Diff_mono[OF _ subset_refl])
     apply (rule UN_mono[OF subset_refl])
    sorry



       prefer 3
  subgoal for d f g
    apply (unfold0 comp_apply case_prod_beta fst_conv snd_conv prod.inject)
    apply (rule conjI)
     apply (rule permute_comps; assumption)
    apply (rule trans[OF comp_apply[symmetric] compSS_comp0])
         apply (rule infinite_UNIV | assumption)+
    done

    sorry

definition vvsubst :: "('a::covar \<Rightarrow> 'a) \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "vvsubst f t = vvsubst.COREC (t, f)"

lemma vvsubst_ctor: "|supp (f::'a::covar \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> set2_term_pre x \<inter> imsupp f = {} \<Longrightarrow>
  vvsubst f (term_ctor x) = term_ctor (map_term_pre f id (vvsubst f) (vvsubst f) x)"
  apply (unfold vvsubst_def)
  apply (rule trans[OF vvsubst.COREC_DDTOR])
    apply (unfold valid_U_vvsubst_def Udtor_vvsubst_def prod.case)[2]
    apply assumption
   apply (rule CollectI)
   apply (rule exI)
   apply (rule conjI refl | assumption)+
  apply (subst term_pre.map_comp)
     apply (rule supp_id_bound bij_id | assumption)+
  apply (unfold id_o o_id)
  apply (unfold comp_def sum.case)
  apply (rule refl)
  done

lemma vvsubst_simps:
  fixes f::"'a::covar \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|"
  shows "vvsubst f (Var a) = Var (f a)"
    "vvsubst f (App t1 t2) = App (vvsubst f t1) (vvsubst f t2)"
  "x \<notin> imsupp f \<Longrightarrow> vvsubst f (Lam x t) = Lam x (vvsubst f t)"
    apply (unfold Var_def App_def Lam_def)
    apply (rule trans[OF vvsubst_ctor])
      apply (rule assms)
     apply (unfold set2_term_pre_def prod.set_map sum.set_map Un_empty_left UN_empty UN_empty2 Un_empty_right comp_def
  Abs_term_pre_inverse[OF UNIV_I] UN_singleton sum_set_simps map_term_pre_def map_sum.simps
)[2]
     apply (rule Int_empty_left)
    apply (rule refl)

    apply (rule trans[OF vvsubst_ctor])
      apply (rule assms)
     apply (unfold set2_term_pre_def prod.set_map sum.set_map Un_empty_left UN_empty UN_empty2 Un_empty_right comp_def
  Abs_term_pre_inverse[OF UNIV_I] UN_singleton sum_set_simps map_term_pre_def map_sum.simps UN_single map_prod_simp
)[2]
     apply (rule Int_empty_left)
   apply (rule refl)

    apply (rule trans[OF vvsubst_ctor])
      apply (rule assms)
     apply (unfold set2_term_pre_def prod.set_map sum.set_map Un_empty_left UN_empty UN_empty2 Un_empty_right comp_def
  Abs_term_pre_inverse[OF UNIV_I] UN_singleton sum_set_simps map_term_pre_def map_sum.simps UN_single map_prod_simp prod_set_simps
  disjoint_single
)[2]
   apply assumption
  apply (unfold id_def)
  apply (rule refl)
  done

mrbnf "'a::covar term"
  map: vvsubst
  sets:
    free: FVars_term
  bd: natLeq
  sorry
print_theorems

end