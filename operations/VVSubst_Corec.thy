theory VVSubst_Corec
  imports "./Corecursor"
begin

lemma insert_subset_Collect: "insert x A \<subseteq> Collect P \<longleftrightarrow> P x \<and> A \<subseteq> Collect P"
  by blast

lemma TT_fresh_inject:
  fixes A::"'a::covar set"
  assumes "|A| <o |UNIV::'a set|" "set2_term_pre x \<inter> A = {}"
  shows "set2_term_pre y \<inter> A = {} \<Longrightarrow> term_ctor x = term_ctor y \<longleftrightarrow> (\<exists>f. bij f \<and> |supp f| <o |UNIV::'a set| \<and>
    id_on (\<Union>(FVars_term ` set3_term_pre x) - set2_term_pre x) f \<and> imsupp f \<inter> A = {}
    \<and> map_term_pre id f (permute_term f) id x = y)"
  apply (rule trans)
   apply (rule TT_inject0s)
  apply (rule iffI[symmetric])
   apply (erule exE conjE)+
   apply (rule exI)
   apply ((rule conjI)?, assumption)+
  apply (erule exE conjE)+
  apply (frule ex_avoiding_bij[rotated 4, of _ _ "set2_term_pre x" A])
         apply (rule term_pre.set_bd_UNIV)
        apply (rule assms)+
      apply assumption+
    apply (rule infinite_UNIV)
   apply (rule ordLeq_ordLess_trans[OF card_of_diff])
   apply (rule var_class.UN_bound)
    apply (rule ordLess_ordLeq_trans)
     apply (rule term_pre.set_bd)
    apply (rule var_class.large')
   apply (rule FVars_bd_UNIVs)
  apply (erule exE conjE)+
  apply (rotate_tac 4)
  apply (rule exI)
  apply (rule conjI, assumption)+
  apply hypsubst_thin
  apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id | assumption)+)
  apply (rule term_pre.map_cong0)
           apply (rule supp_id_bound bij_id refl | assumption)+
    apply (erule allE)
    apply (erule mp)
    apply (rule conjI)
     apply (erule UnI2)
    apply (rotate_tac 4)
    apply (drule iffD1[OF disjoint_iff])
    apply (erule allE)
    apply (erule mp)
    apply (erule imageI)

    apply (rule permute_congs)
        apply assumption+
   apply (rule case_split[of "_ \<in> _", rotated])
    apply (rule trans)
     apply (erule id_onD)
     apply (rule DiffI)
      apply (rule UN_I)
       apply assumption+
    apply (rule sym)
    apply (erule id_onD)
    apply (rule DiffI UN_I | assumption)+
   apply (erule allE)
   apply (erule mp)
   apply (rule conjI)
  apply (erule UnI2)
    apply (rotate_tac 4)
    apply (drule iffD1[OF disjoint_iff])
    apply (erule allE)
    apply (erule mp)
   apply (erule imageI)
  apply (rule refl)
  done

type_synonym 'a U = "'a term \<times> ('a \<Rightarrow> 'a)"

definition Udtor_vvsubst :: "'a U \<Rightarrow> ('a::covar, 'a, 'a term + 'a U, 'a term + 'a U) term_pre set" where
  "Udtor_vvsubst p = (case p of (t, f) \<Rightarrow> { map_term_pre f id (\<lambda>t. Inr (t, f)) (\<lambda>t. Inr (t, f))
    t' | t'. t = term_ctor t' \<and> set2_term_pre t' \<inter> imsupp f = {} }
  )"

definition Umap_vvsubst :: "('a::covar \<Rightarrow> 'a) \<Rightarrow> 'a U \<Rightarrow> 'a U" where
  "Umap_vvsubst g p = (case p of (t, f) \<Rightarrow>
    (permute_term g t, g \<circ> f \<circ> inv g)
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
    apply (rotate_tac -1)
    apply (erule thin_rl)
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

    apply (drule TT_fresh_inject[THEN iffD1, rotated -1, OF trans, OF sym])
        apply assumption
       prefer 2
       apply assumption
      apply (rule iffD2[OF imsupp_supp_bound])
       apply (rule infinite_UNIV)
      apply assumption
     apply assumption

    apply (erule exE conjE)+
    apply hypsubst
    apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id | assumption)+)
    apply (rule exI)+
    apply (rule conjI, assumption)+
    apply (subst term_pre.map_comp, (rule supp_id_bound bij_id | assumption)+)+
    apply (unfold id_o o_id)
    apply (unfold comp_def[of "\<lambda>t. Inr (_ t)"] comp_def[of _ "\<lambda>t. Inr (_ t)"] map_sum.simps fst_conv snd_conv)
    apply (rule conjI)
    apply (subst UN_simps(2))
    apply (rule case_split)
     apply (subst if_P)
      apply assumption
      apply (unfold empty_Diff)
      apply (rule id_on_empty)
     apply (unfold if_not_P)
     apply (subst Diff_Un_disjunct[symmetric])
      apply assumption
     apply (rule iffD2[OF id_on_Un])
     apply (erule conjI)
     apply (rule imsupp_id_on)
     apply assumption
    apply (rule term_pre.map_cong0)
    apply (assumption | rule refl)+

     apply (unfold sum.inject prod.inject comp_assoc)[1]
     apply (rule conjI)
      apply (rule refl)
     apply (rule trans)
      apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
      apply (rule imsupp_commute)
      apply (rule trans[OF Int_commute])
      apply (unfold imsupp_inv)
      apply assumption
     apply (unfold comp_assoc[symmetric])[1]
     apply (subst inv_o_simp2)
      apply assumption
    apply (rule id_o)
    apply (rule refl)
    done

  subgoal for d X
       apply (unfold mem_Collect_eq)
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (subst term_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
    apply (unfold image_id image_comp[unfolded comp_def] sum.case fst_conv snd_conv)
    apply (erule subst[OF sym])
    apply (unfold FVars_ctors)
    apply (rule Un_mono')+
      apply (rule subset_trans[OF image_imsupp_subset])
      apply (rule Un_commute[THEN equalityD1])
     apply (subst UN_simps(2))
     apply (rule case_split)
      apply (subst if_P)
       apply assumption
      apply (unfold empty_Diff)
      apply (rule empty_subsetI)
     apply (unfold if_not_P)
     apply (subst Diff_Un_disjunct[symmetric])
      apply assumption
    apply (rule subset_refl)
     apply (subst UN_simps(2))
     apply (rule case_split)
      apply (subst if_P)
       apply assumption
      apply (rule empty_subsetI)
    apply (unfold if_not_P)
    apply (rule subset_refl)
    done

  subgoal for u d
    apply (rule subsetI)
    apply (unfold mem_Collect_eq image_Collect)
    apply (erule exE conjE)+
    apply hypsubst
    apply (unfold triv_forall_equality)
    subgoal for t'
    apply (rule fresh_cases[of "imsupp u \<union> imsupp (snd d) \<union> set2_term_pre t'" "fst d"])
    apply (rule infinite_class.Un_bound iffD2[OF imsupp_supp_bound] infinite_UNIV term_pre.set_bd_UNIV | assumption)+
    apply (rotate_tac -1)
    apply (erule thin_rl)

    apply (drule trans[rotated])
     apply (rule sym)
    apply (rotate_tac -2)
     apply (erule arg_cong)
    apply (subst (asm) permute_simps)
      apply assumption+
    apply (unfold Int_Un_distrib Un_empty)
    apply (erule conjE)+

      apply (unfold TT_inject0s)
    apply (erule exE conjE)+
    apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
    apply (unfold image_comp[unfolded comp_def])
    apply (subst (asm) FVars_permutes term_pre.map_comp, (rule supp_id_bound bij_id | assumption)+)+
    apply (unfold image_UN[symmetric] image_set_diff[symmetric, OF bij_is_inj] id_o permute_comp0s)
    apply hypsubst_thin
    apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | assumption)+)+
    subgoal for x g

    apply (subst term_pre.map_comp, (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV supp_inv_bound | assumption)+)+
      apply (unfold id_o o_id comp_assoc inv_o_simp1 comp_def[of "\<lambda>t. Inr (_ t)"] comp_def[of _ "\<lambda>t. Inr (_ t)"])
      apply (unfold comp_assoc[symmetric])

      apply (rule exI[of _ "map_term_pre (snd d) (inv u \<circ> g \<circ> u) (\<lambda>t. Inr (permute_term (inv u \<circ> g \<circ> u) t, snd d)) (\<lambda>t. Inr (t, snd d)) x"])
      apply (rule conjI[rotated])
       apply (rule exI[of _ "map_term_pre id (inv u \<circ> g \<circ> u) (permute_term (inv u \<circ> g \<circ> u)) id x"])
       apply (rule conjI)
        apply (subst term_pre.map_comp, (rule supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_comp_bound infinite_UNIV supp_inv_bound | assumption)+)
        apply (unfold id_o o_id)
        apply (unfold comp_def)[1]
      apply (rule refl)

       apply (rule conjI)
        apply (rule trans)
         apply assumption
        apply (rule sym)
        apply (rule iffD2[OF TT_inject0s])
        apply (rule exI[of _ "inv (inv u \<circ> g \<circ> u)"])
        apply (rule conjI bij_imp_bij_inv bij_comp supp_inv_bound supp_comp_bound infinite_UNIV | assumption)+
         apply (rule id_on_inv)
          apply (rule bij_comp bij_imp_bij_inv | assumption)+
         apply (subst term_pre.set_map, (rule supp_id_bound bij_id bij_imp_bij_inv bij_comp supp_inv_bound supp_comp_bound infinite_UNIV | assumption)+)+
         apply (unfold image_comp[unfolded comp_def])
         apply (subst FVars_permutes, (rule supp_id_bound bij_id bij_imp_bij_inv bij_comp supp_inv_bound supp_comp_bound infinite_UNIV | assumption)+)+
         apply (unfold image_UN[symmetric])
      apply (subst image_set_diff[OF bij_is_inj, symmetric])
          apply (rule bij_comp bij_imp_bij_inv | assumption)+
         apply (rule id_on_image_same)
         apply (rule id_on_inv_f_f)
          apply assumption+

        apply (subst term_pre.map_comp inv_o_simp1 permute_comp0s, (rule supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_comp_bound infinite_UNIV supp_inv_bound | assumption)+)+
        apply (unfold id_o permute_id0s)
        apply (rule term_pre.map_id)
       apply (subst term_pre.set_map, (rule supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_comp_bound infinite_UNIV supp_inv_bound | assumption)+)

       prefer 2
       apply (subst term_pre.map_comp, (rule supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_comp_bound infinite_UNIV supp_inv_bound | assumption)+)+
       apply (unfold comp_assoc[symmetric])
       apply (subst inv_o_simp2, assumption)
       apply (unfold id_o comp_def[of "\<lambda>t. Inr (_ t)"] comp_def[of _ "\<lambda>t. Inr (_ t)"] map_sum.simps fst_conv snd_conv)
      apply (subst permute_comps, (rule supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_comp_bound infinite_UNIV supp_inv_bound | assumption)+)+
       apply (unfold comp_assoc[symmetric])
       apply (subst inv_o_simp2, assumption)
       apply (unfold id_o)
       apply (rule refl)

      apply (unfold comp_assoc)
      apply (subst image_comp[symmetric])
      apply (rule iffD2[OF image_Int_empty_inv])
       apply (rule bij_imp_bij_inv)
       apply assumption
      apply (unfold inv_inv_eq)
      apply (unfold comp_assoc[symmetric])
      apply (subst (asm) imsupp_comp_image)
       apply assumption
      apply assumption
      done
    done
  done

  subgoal for d f g
    apply (unfold0 comp_apply case_prod_beta fst_conv snd_conv prod.inject)
    apply (rule conjI)
     apply (rule permute_comps; assumption)
    apply (unfold comp_assoc o_inv_distrib)
    apply (rule refl)
    done

    apply (subst permute_cong_ids)
       apply assumption+
     apply (drule meta_spec)
     apply (drule meta_mp)
      apply (erule UnI1)
     apply assumption
    apply (subst compSS_cong_id[unfolded compSS_def])
  apply assumption+
     apply (drule meta_spec)
     apply (drule meta_mp)
  apply (erule UnI2)
     apply assumption
    apply (rule prod.collapse)
  apply (rule supp_comp_bound infinite_UNIV supp_inv_bound | assumption)+

  subgoal for d x
    apply (unfold mem_Collect_eq)
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (rule iffD2[OF term_pre.pred_map])
       apply (rule bij_id supp_id_bound | assumption)+
    apply (unfold comp_def pred_sum_inject snd_conv term_pre.pred_set)
    apply (rule conjI ballI | assumption)+
    done
  done

definition vvsubst :: "('a::covar \<Rightarrow> 'a) \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "vvsubst f t = vvsubst.COREC (t, f)"

lemma vvsubst_ctor: "|supp (f::'a::covar \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> set2_term_pre x \<inter> imsupp f = {} \<Longrightarrow>
  vvsubst f (term_ctor x) = term_ctor (map_term_pre f id (vvsubst f) (vvsubst f) x)"
  apply (unfold vvsubst_def)
  apply (rule trans[OF vvsubst.COREC_DDTOR])
    apply (unfold valid_U_vvsubst_def Udtor_vvsubst_def prod.case)[2]
   apply (rule CollectI)
   apply (rule exI)
   apply (rule conjI refl | assumption)+
  apply (subst term_pre.map_comp)
     apply (rule supp_id_bound bij_id | assumption)+
  apply (unfold id_o o_id)
  apply (unfold comp_def sum.case)
  apply (rule refl)
  done

definition Var :: "'a::covar \<Rightarrow> 'a term" where
  "Var a = term_ctor (Abs_term_pre (Inl a))"
definition App :: "'a::covar term \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "App t1 t2 = term_ctor (Abs_term_pre (Inr (Inl (t1, t2))))"
definition Lam :: "'a::covar \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "Lam a t = term_ctor (Abs_term_pre (Inr (Inr (a, t))))"

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

lemma vvsubst_permute:
  fixes f::"'a::covar \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "vvsubst f = permute_term f"
  apply (rule ext)
  apply (rule existential_coinduct[of "\<lambda>l r. \<exists>y. l = vvsubst f y \<and> r = permute_term f y"])
   apply (rule exI, (rule conjI refl)+)
  apply (unfold triv_forall_equality)
  apply (erule exE conjE)+
  subgoal for xa y ya
    apply (rule fresh_cases[of "imsupp f" ya])
     apply (rule iffD2[OF imsupp_supp_bound])
      apply (rule infinite_UNIV)
     apply (rule assms)
    apply hypsubst_thin
    apply (subst (asm) vvsubst_ctor)
      apply (rule assms)
     apply assumption
    apply (subst (asm) permute_simps)
      apply (rule assms)+
    apply (rule exI)+
    apply (rule conjI, erule sym)+
    apply (unfold term_pre.mr_rel_id)
    apply (rule iffD2[OF term_pre.mr_rel_map(1)])
          apply (rule assms supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (subst term_pre.map_cong0[rotated -4])
             apply (rule refl)
            apply (drule trans[OF Int_commute])
            apply (erule imsupp_id_on[THEN id_onD])
            apply assumption
           apply (unfold id_def[symmetric])
           apply (rule refl assms bij_id supp_id_bound)+

    apply (rule iffD2[OF term_pre.mr_rel_map(3)])
           apply (rule assms supp_id_bound bij_id)+
    apply (subst inv_o_simp1, rule assms)
    apply (unfold o_id relcompp_conversep_Grp inv_id)
    apply (unfold Grp_OO)
    apply (unfold term_pre.mr_rel_id[symmetric])
    apply (rule term_pre.rel_refl_strong)
     apply (rule disjI1 exI conjI refl)+
    done
  done

corollary vvsubst_id: "vvsubst id = id"
  apply (rule trans)
   apply (rule vvsubst_permute)
    apply (rule bij_id supp_id_bound)+
  apply (rule permute_id0s)
  done

lemma vvsubst_comp0:
  fixes f g::"'a::covar \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|" "|supp g| <o |UNIV::'a set|"
  shows "vvsubst f \<circ> vvsubst g = vvsubst (f \<circ> g)"
  apply (rule ext)
  apply (rule existential_coinduct[of "\<lambda>l r. \<exists>y. l = vvsubst f (vvsubst g y) \<and> r = vvsubst (f \<circ> g) y"])
   apply (rule exI)
   apply (unfold comp_apply)[1]
   apply (rule conjI refl)+

  apply (erule exE conjE)+
  apply (unfold triv_forall_equality)
  subgoal for xa y ya
    apply (rule fresh_cases[of "imsupp f \<union> imsupp g" ya])
     apply (rule infinite_class.Un_bound)
      apply (rule iffD2[OF imsupp_supp_bound] infinite_UNIV assms)+
    apply hypsubst_thin
    apply (subst (asm) vvsubst_ctor)
      apply (rule assms)
     apply (erule Int_subset_empty2)
     apply (rule Un_upper2)
    apply (subst (asm) vvsubst_ctor)
      apply (rule assms)
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id assms)+)
     apply (unfold image_id)
     apply (erule Int_subset_empty2)
     apply (rule Un_upper1)
    apply (subst (asm) vvsubst_ctor)
      apply (rule supp_comp_bound infinite_UNIV assms)+
     apply (erule Int_subset_empty2)
     apply (rule imsupp_o)
    apply (rule exI)+
    apply (rule conjI, erule sym)+
    apply (subst term_pre.map_comp)
        apply (rule assms supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (subst (2) term_pre.map_comp[of _ _ id id _ _ id id, unfolded id_o o_id, symmetric])
    apply (rule supp_comp_bound bij_comp bij_id supp_id_bound assms infinite_UNIV)+
    apply (subst term_pre.map_comp[of _ _ id id _ _ id id, unfolded id_o o_id, symmetric])
       apply (rule supp_comp_bound bij_comp bij_id supp_id_bound assms infinite_UNIV)+
    apply (unfold term_pre.rel_map)
    apply (rule term_pre.rel_refl_strong)
     apply (unfold comp_def)
     apply (rule disjI1 exI conjI refl)+
    done
  done

lemma vvsubst_cong0:
  fixes f g::"'a::covar \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|" "|supp g| <o |UNIV::'a set|"
  and "\<And>a. a \<in> FVars_term x \<Longrightarrow> f a = g a"
  shows "vvsubst f x = vvsubst g x"
  apply (rule existential_coinduct[of "\<lambda>l r. \<exists>y. (\<forall>a. a \<in> FVars_term y \<longrightarrow> f a = g a) \<and> l = vvsubst f y \<and> r = vvsubst g y"])
   apply (rule exI)
   apply (rule conjI refl allI impI assms | assumption)+

  apply (erule exE conjE)+
  subgoal for x y z
    apply (rule fresh_cases[of "imsupp f \<union> imsupp g" z])
     apply (rule infinite_class.Un_bound)
      apply (rule iffD2[OF imsupp_supp_bound] infinite_UNIV assms)+
    apply hypsubst_thin
    apply (subst (asm) vvsubst_ctor)
      apply (rule assms)
     apply (erule Int_subset_empty2)
    apply (rule Un_upper1)
    apply (subst (asm) vvsubst_ctor)
      apply (rule assms)
     apply (erule Int_subset_empty2)
     apply (rule Un_upper2)
    apply (rule exI)+
    apply (rule conjI, erule sym)+
    apply (subst (2) term_pre.map_comp[of _ _ id id _ _ id id, unfolded id_o o_id, symmetric])
    apply (rule assms supp_id_bound bij_id)+
    apply (subst term_pre.map_comp[of _ _ id id _ _ id id, unfolded id_o o_id, symmetric])
       apply (rule assms supp_id_bound bij_id)+
    apply (unfold term_pre.rel_map)
    apply (subst term_pre.map_cong0[rotated -4])
              apply (erule allE)
              apply (erule mp)
              apply (erule FVars_intros)
             apply (rule refl)+
          apply (rule assms supp_id_bound bij_id)+
    apply (rule term_pre.rel_refl_strong)
    (* REPEAT_DETERM *)
     apply (subst (asm) term_pre.set_map, (rule assms supp_id_bound bij_id)+)
    apply (unfold image_id)
     apply (rule disjI1)
     apply (rule exI)
     apply (rule conjI[rotated])+
       apply (rule refl)+
     apply (rule allI)
     apply (rule impI)
     apply (rule case_split[of "_ \<in> _", rotated])
      apply (erule allE)
      apply (erule mp)
      apply (erule FVars_intros)
       apply assumption
      apply assumption
     apply (rule trans)
      apply (rotate_tac -1)
      apply (erule imsupp_id_on[THEN id_onD, rotated])
      apply (rule trans[OF Int_commute])
      apply (erule Int_subset_empty2)
      apply (rule Un_upper1)
    apply (rule sym)
      apply (rotate_tac -1)
      apply (erule imsupp_id_on[THEN id_onD, rotated])
      apply (rule trans[OF Int_commute])
      apply (erule Int_subset_empty2)
     apply (rule Un_upper2)
  (* repeated *)
     apply (subst (asm) term_pre.set_map, (rule assms supp_id_bound bij_id)+)
    apply (unfold image_id)
     apply (rule disjI1)
     apply (rule exI)
     apply (rule conjI[rotated])+
       apply (rule refl)+
     apply (rule allI)
     apply (rule impI)
      apply (erule allE)
      apply (erule mp)
      apply (erule FVars_intros)
    apply assumption
    done
  done

lemma FVars_induct:
  assumes "a \<in> FVars_term t"
  and "\<And>a x. a \<in> set1_term_pre x \<Longrightarrow> P a (term_ctor x)"
  and "\<And>a z x. z \<in> set3_term_pre x \<Longrightarrow> a \<in> FVars_term z \<Longrightarrow> P a z \<Longrightarrow> a \<notin> set2_term_pre x \<Longrightarrow> P a (term_ctor x)"
  and "\<And>a z x. z \<in> set4_term_pre x \<Longrightarrow> a \<in> FVars_term z \<Longrightarrow> P a z \<Longrightarrow> P a (term_ctor x)"
shows "P a t"
  apply (insert assms(1))
  apply (unfold FVars_term_def atomize_imp)
  apply (rule Quotient_total_abs_induct[OF TT_Quotients reflpI[OF alpha_refls]])
  apply (unfold alpha_FVars[OF TT_rep_abs])

  apply (unfold FVars_raw_term_def mem_Collect_eq)
  apply (rule impI)
  apply (erule free_raw_term.induct)
    apply (insert assms(2)[of _ "map_term_pre id id TT_abs TT_abs _"])[1]
    apply (subst (asm) term_pre.set_map)
      apply (rule supp_id_bound bij_id)+
    apply (unfold image_id)
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply assumption
    apply (unfold term_ctor_def)[1]
    apply (subst (asm) term_pre.map_comp)
      apply (rule supp_id_bound bij_id)+
    apply (unfold id_o)
    apply (subst (asm) TT_total_abs_eq_iffs[THEN iffD2])
     apply (rule alpha_term.intros)
        apply (rule supp_id_bound bij_id id_on_id)+
     apply (unfold term_pre.mr_rel_id[symmetric] term_pre.rel_map permute_raw_ids)
     apply (rule term_pre.rel_refl_strong)
      apply (unfold comp_def)[1]
  apply (rule TT_rep_abs)
      apply (unfold comp_def)[1]
     apply (rule TT_rep_abs)
    apply assumption

  apply (insert assms(3)[of _ "map_term_pre id id TT_abs TT_abs _"])[1]
   apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id)
   apply (drule imageI)
   apply (drule meta_spec)+
   apply (drule meta_mp)
    apply assumption
   apply (drule meta_mp)
    apply (unfold FVars_term_def alpha_FVars[OF TT_rep_abs])[1]
    apply (unfold FVars_raw_term_def mem_Collect_eq)[1]
    apply assumption
   apply (drule meta_mp)
    apply assumption
   apply (drule meta_mp)
    apply assumption
    apply (unfold term_ctor_def)[1]
    apply (subst (asm) term_pre.map_comp)
      apply (rule supp_id_bound bij_id)+
   apply (unfold id_o)
  apply (rotate_tac -1)
    apply (subst (asm) TT_total_abs_eq_iffs[THEN iffD2])
     apply (rule alpha_term.intros)
        apply (rule supp_id_bound bij_id id_on_id)+
     apply (unfold term_pre.mr_rel_id[symmetric] term_pre.rel_map permute_raw_ids)
     apply (rule term_pre.rel_refl_strong)
      apply (unfold comp_def)[1]
  apply (rule TT_rep_abs)
      apply (unfold comp_def)[1]
     apply (rule TT_rep_abs)
   apply assumption

  apply (insert assms(4)[of _ "map_term_pre id id TT_abs TT_abs _"])[1]
   apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (drule imageI)
   apply (drule meta_spec)+
   apply (drule meta_mp)
    apply assumption
   apply (drule meta_mp)
    apply (unfold FVars_term_def alpha_FVars[OF TT_rep_abs])[1]
    apply (unfold FVars_raw_term_def mem_Collect_eq)[1]
    apply assumption
   apply (drule meta_mp)
    apply assumption
    apply (unfold term_ctor_def)[1]
    apply (subst (asm) term_pre.map_comp)
      apply (rule supp_id_bound bij_id)+
   apply (unfold id_o)
  apply (rotate_tac -1)
    apply (subst (asm) TT_total_abs_eq_iffs[THEN iffD2])
     apply (rule alpha_term.intros)
        apply (rule supp_id_bound bij_id id_on_id)+
     apply (unfold term_pre.mr_rel_id[symmetric] term_pre.rel_map permute_raw_ids)
     apply (rule term_pre.rel_refl_strong)
      apply (unfold comp_def)[1]
  apply (rule TT_rep_abs)
      apply (unfold comp_def)[1]
     apply (rule TT_rep_abs)
  apply assumption
  done

lemma FVars_fresh_induct_param:
  fixes a::"'a::covar"
  assumes "a \<in> FVars_term t" "\<And>\<rho>. \<rho> \<in> Param \<Longrightarrow> |K \<rho>| <o |UNIV::'a set|"
  and "\<And>a x \<rho>. a \<in> set1_term_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> set2_term_pre x \<inter> K \<rho> = {} \<Longrightarrow> noclash_term x \<Longrightarrow> P a (term_ctor x) \<rho>"
  and "\<And>a z x \<rho>. z \<in> set3_term_pre x \<Longrightarrow> a \<in> FVars_term z \<Longrightarrow> \<forall>\<rho>\<in>Param. P a z \<rho> \<Longrightarrow> a \<notin> set2_term_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> set2_term_pre x \<inter> K \<rho> = {} \<Longrightarrow> noclash_term x \<Longrightarrow> P a (term_ctor x) \<rho>"
  and "\<And>a z x \<rho>. z \<in> set4_term_pre x \<Longrightarrow> a \<in> FVars_term z \<Longrightarrow> \<forall>\<rho>\<in>Param. P a z \<rho> \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> set2_term_pre x \<inter> K \<rho> = {} \<Longrightarrow> noclash_term x \<Longrightarrow> P a (term_ctor x) \<rho>"
shows "\<forall>\<rho>\<in>Param. P a t \<rho>"
  apply (rule FVars_induct[of a t "\<lambda>a t. \<forall>f. bij f \<longrightarrow> |supp f| <o |UNIV::'a set| \<longrightarrow> (\<forall>\<rho>\<in>Param. P (f a) (permute_term f t) \<rho>)", THEN spec, THEN mp[OF _ bij_id], THEN mp[OF _ supp_id_bound], unfolded permute_ids, unfolded id_apply])
     apply (rule assms)
  apply (rule allI impI ballI)+
  subgoal for a x f \<rho>
    apply (rule fresh_cases[of "K \<rho>" "permute_term f (term_ctor x)"])
     apply (erule assms)
    apply (rule arg_cong3[OF refl _ refl, THEN iffD2, of _ _ P])
     apply assumption
    apply (rule assms(3)[rotated])
       apply assumption+
    apply (unfold permute_simps TT_inject0s)
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (subst (asm) term_pre.set_map, (rule supp_id_bound | assumption)+)+
    apply (subst term_pre.set_map, (rule supp_id_bound | assumption)+)+
    apply (unfold image_id)
    apply (rule imageI)
    apply assumption
    done

   apply (rule allI impI ballI)+
  subgoal for a z x f \<rho>
    apply (rule fresh_cases[of "K \<rho> \<union> {f a}" "permute_term f (term_ctor x)"])
    apply (rule infinite_class.Un_bound)
      apply (erule assms)
    apply (rule single_bound)
    
    apply (rule arg_cong3[OF refl _ refl, THEN iffD2, of _ _ P])
     apply assumption
    apply (unfold permute_simps)
    apply (drule iffD1[OF TT_fresh_inject[of "{f a}", OF single_bound], rotated -1])
      apply (subst term_pre.set_map, assumption+)
      apply (unfold image_single[of f] image_Int[OF bij_is_inj, symmetric] image_is_empty)[1]
      apply (rule trans[OF Int_commute])
      apply (rule iffD2[OF disjoint_single])
      apply assumption
     apply (erule Int_subset_empty2)
    apply (rule Un_upper2)

    apply (erule exE conjE)+
    apply hypsubst
    apply (subst (asm) term_pre.set_map, (rule supp_id_bound | assumption)+)+
    apply (subst (asm) image_comp)
    apply (unfold image_comp[unfolded comp_def])
    apply (subst (asm) FVars_permutes, (rule supp_id_bound | assumption)+)+
    apply (unfold image_UN[symmetric] image_set_diff[OF bij_is_inj, symmetric])
    apply (rule assms(4))
          apply (rule arg_cong2[OF refl _, of _ _ "(\<in>)", THEN iffD2], rule term_pre.set_map, (rule supp_id_bound | assumption)+)
    apply (rule imageI)
          apply (rule arg_cong2[OF refl _, of _ _ "(\<in>)", THEN iffD2], rule term_pre.set_map, (rule supp_id_bound | assumption)+)
          apply (rule imageI)
          apply assumption
         apply (subst permute_comps, assumption+)
         apply (subst FVars_permutes)
           apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
         apply (rule iffD2[OF image_in_bij_eq])
          apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
         apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]])
          apply (unfold o_inv_distrib)
          apply (rule trans[OF comp_apply])
          apply (rule arg_cong[of _ _ "inv _"])
          apply (erule id_on_inv[THEN id_onD, rotated])
           apply (rule imageI)
           apply (rule DiffI)
            apply (rule UN_I)
             apply assumption+
         apply (unfold inv_simp1)
         apply assumption

        apply (subst permute_comps, assumption+)
        apply (rule arg_cong[of _ _ "Ball Param", THEN iffD2])
         apply (rule arg_cong2[OF _ refl, of _ _ P])
         apply (rule sym)
         apply (rotate_tac -1)
         apply (drule imsupp_id_on)
         apply (erule id_onD[OF _ singletonI])
        apply (unfold comp_def triv_forall_equality)[1]
    subgoal for g
      apply (erule allE[of _ "g \<circ> f"])
      apply (erule impE, (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+)+
      apply (unfold comp_def)[1]
      apply assumption
      done

       apply (subst term_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
       apply (unfold image_comp)
       apply (rule disjoint_iff[THEN iffD1, THEN spec, THEN mp])
        apply (erule trans[OF Int_commute])
       apply (rule UnI2)
       apply (rule singletonI)
      apply assumption

       apply (subst term_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
     apply (unfold image_comp)
     apply (erule Int_subset_empty2)
     apply (rule Un_upper1)
    apply assumption
    done

  apply (rule allI impI ballI)+
  subgoal for a z x f \<rho>
    apply (rule fresh_cases[of "K \<rho>" "permute_term f (term_ctor x)"])
     apply (erule assms)
    apply (rule arg_cong3[OF refl _ refl, THEN iffD2, of _ _ P])
     apply assumption
    apply (unfold permute_simps TT_inject0s)
    apply (erule exE conjE)+
    apply hypsubst
    apply (subst (asm) term_pre.set_map, (rule supp_id_bound | assumption)+)+
    apply (subst (asm) image_comp)
    apply (unfold image_comp[unfolded comp_def])
    apply (subst (asm) FVars_permutes, (rule supp_id_bound | assumption)+)+
    apply (unfold image_UN[symmetric] image_set_diff[OF bij_is_inj, symmetric])
    apply (rule assms(5))
          apply (rule arg_cong2[OF refl _, of _ _ "(\<in>)", THEN iffD2], rule term_pre.set_map, (rule supp_id_bound | assumption)+)
    apply (rule imageI)
          apply (rule arg_cong2[OF refl _, of _ _ "(\<in>)", THEN iffD2], rule term_pre.set_map, (rule supp_id_bound | assumption)+)
          apply (rule imageI)
         apply assumption
        apply (unfold0 id_apply)
         apply (subst FVars_permutes)
           apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
         apply (rule iffD2[OF image_in_bij_eq])
          apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
         apply (unfold inv_simp1)
         apply assumption

       apply (erule allE)
       apply (erule impE, assumption)+
       apply assumption+

     apply (subst term_pre.set_map, (rule supp_id_bound | assumption)+)+
     apply (unfold image_comp)
     apply assumption
    apply assumption
    done
  done

lemma FVars_fresh_induct:
  assumes "a \<in> FVars_term t" "|A::'a set| <o |UNIV::'a::covar set|"
  and "\<And>a x. a \<in> set1_term_pre x \<Longrightarrow> set2_term_pre x \<inter> A = {} \<Longrightarrow> noclash_term x \<Longrightarrow> P a (term_ctor x)"
  and "\<And>a z x. z \<in> set3_term_pre x \<Longrightarrow> a \<in> FVars_term z \<Longrightarrow> P a z \<Longrightarrow> a \<notin> set2_term_pre x \<Longrightarrow> set2_term_pre x \<inter> A = {} \<Longrightarrow> noclash_term x \<Longrightarrow> P a (term_ctor x)"
  and "\<And>a z x. z \<in> set4_term_pre x \<Longrightarrow> a \<in> FVars_term z \<Longrightarrow> P a z \<Longrightarrow> set2_term_pre x \<inter> A = {} \<Longrightarrow> noclash_term x \<Longrightarrow> P a (term_ctor x)"
shows "P a t"
  apply (rule FVars_fresh_induct_param[of _ _ UNIV, unfolded ball_UNIV, THEN spec, of _ _ "\<lambda>_. A" "\<lambda>a t _. P a t"])
      apply (rule assms)+
      apply assumption+
   apply (drule assms)
        apply assumption+
       apply (erule allE)
  apply assumption+
   apply (drule assms)
        apply assumption+
       apply (erule allE)
     apply assumption+
  done

lemma imsupp_notin: "a \<notin> A \<Longrightarrow> imsupp f \<inter> A = {} \<Longrightarrow> f a \<notin> A"
  unfolding imsupp_def supp_def by force

lemma FVars_vvsubst:
  fixes f::"'a::covar \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|"
  shows "FVars_term (vvsubst f x) = f ` FVars_term x"
  apply (rule set_eqI)
  apply (rule iffI[rotated])

   apply (erule imageE)
   apply hypsubst
   apply (erule FVars_fresh_induct[of _ _ "imsupp f"])
      apply (rule iffD2[OF imsupp_supp_bound])
       apply (rule infinite_UNIV)
      apply (rule assms)
     apply (subst vvsubst_ctor)
       apply (rule assms)
      apply assumption
     apply (rule FVars_intros(1))
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id assms)+)
     apply (erule imageI)

     apply (subst vvsubst_ctor)
       apply (rule assms)
     apply assumption
    apply (rule FVars_intros(2)[rotated])
      apply assumption
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id assms)+)
     apply (unfold image_id)
     apply (erule imsupp_notin)
  apply (erule trans[OF Int_commute])
    apply (subst term_pre.set_map, (rule supp_id_bound bij_id assms)+)
    apply (rule imageI)
    apply assumption

     apply (subst vvsubst_ctor)
       apply (rule assms)
     apply assumption
    apply (rule FVars_intros(3)[rotated])
      apply assumption
     apply (subst term_pre.set_map, (rule supp_id_bound bij_id assms)+)
    apply (rule imageI)
    apply assumption

  subgoal for a
    apply (drule FVars_fresh_induct[of a "vvsubst f x" "imsupp f" "\<lambda>a t. \<forall>t' g. bij g \<longrightarrow> |supp g| <o |UNIV::'a set| \<longrightarrow> t = permute_term g (vvsubst f t') \<longrightarrow> inv g a \<in> f ` FVars_term t'"])
        apply (rule iffD2[OF imsupp_supp_bound])
       apply (rule infinite_UNIV)
        apply (rule assms)
       prefer 4
       apply (erule allE)+
       apply (erule impE)
        apply (rule bij_id)
       apply (erule impE)
        apply (rule supp_id_bound)
       apply (erule impE)
        apply (rule sym)
        apply (unfold0 permute_ids id_apply inv_id)
    apply (rule refl)
       apply assumption

      apply (rule allI impI)+
    subgoal for a x t'
      apply (rule fresh_cases[of "imsupp f" t'])
       apply (rule iffD2[OF imsupp_supp_bound])
       apply (rule infinite_UNIV)
       apply (rule assms)
      apply hypsubst_thin
      apply (subst (asm) vvsubst_ctor)
        apply (rule assms)
       apply assumption
      apply (rotate_tac -3)
      apply (drule sym)
      apply (unfold permute_simps TT_inject0s)
      apply (erule exE conjE)+
      apply hypsubst_thin

      apply (subst (asm) term_pre.set_map, (rule assms supp_id_bound bij_id | assumption)+)+
      apply (unfold image_id)
      apply (unfold image_comp[unfolded comp_def])
      apply (erule imageE)
      apply hypsubst_thin
      apply (unfold inv_simp1)
      apply (rule imageI)
      apply (erule FVars_intros)
      done

     apply (rule allI impI)+
    subgoal for a z x t' g
      apply (rule fresh_cases[of "inv g ` imsupp f \<union> imsupp f" t'])
       apply (rule ordLeq_ordLess_trans[OF card_of_image] infinite_class.Un_bound iffD2[OF imsupp_supp_bound] infinite_UNIV assms)+
      apply (unfold Int_Un_distrib Un_empty)
      apply (erule conjE)+
      apply hypsubst_thin
      apply (subst (asm) vvsubst_ctor)
        apply (rule assms)
       apply assumption
      apply (rotate_tac -4)
      apply (unfold permute_simps)
      apply (drule sym)
      apply (drule TT_fresh_inject[THEN iffD1, of "imsupp f", rotated -1])
       apply (rule iffD2[OF imsupp_supp_bound])
       apply (rule infinite_UNIV)
         apply (rule assms)
        apply (subst term_pre.set_map, (rule assms supp_id_bound bij_id | assumption)+)+
       apply (unfold image_id)
       apply (rule iffD2[OF image_Int_empty_inv])
        apply assumption+
      apply (erule exE conjE)+
      apply hypsubst_thin

      apply (subst (asm) term_pre.set_map, (rule assms supp_id_bound bij_id | assumption)+)+
      apply (unfold image_id)
      apply (unfold image_comp comp_assoc[symmetric])
      apply (subst (asm) permute_comp0s)
          apply assumption+
      apply (erule imageE)
      apply hypsubst_thin
      apply (unfold0 comp_apply)
      apply (erule allE)+
      apply (erule impE)
       prefer 2
       apply (erule impE)
        prefer 2
        apply (erule impE)
         apply (rule refl)
        apply (subst (asm) image_in_bij_eq[symmetric])
         apply (rule bij_comp)
          apply assumption+
        apply (unfold image_comp)
        apply (erule imageE)
        apply hypsubst_thin
        apply (unfold0 comp_apply)
         apply (subst (asm) FVars_permutes)
           apply (rule bij_comp assms supp_comp_bound infinite_UNIV | assumption)+
      apply (subst (asm) image_in_bij_eq)
          apply (rule bij_comp assms supp_comp_bound infinite_UNIV | assumption)+
      apply (subst (asm) image_in_bij_eq)
          apply (rule bij_comp assms supp_comp_bound infinite_UNIV | assumption)+
         apply (unfold0 o_inv_distrib comp_apply inv_simp1)
        apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
         apply (rule arg_cong[of _ _ "inv _"])
         apply (erule id_onD)
         apply (unfold comp_def FVars_permutes image_UN[symmetric] image_set_diff[OF bij_is_inj, symmetric])[1]
         apply (rule imageI)
         apply (rule DiffI)
          apply (rule UN_I)
           apply assumption+
        apply (unfold0 inv_simp1)
        apply (rule imageI)
        apply (erule FVars_intros)
         apply assumption
        apply (drule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
         apply (rule id_on_image[symmetric])
         apply (rule imsupp_id_on)
         apply (rule trans[OF Int_commute])
         apply assumption
        apply (rotate_tac -1)
        apply (erule contrapos_nn)
        apply (erule imageI)
       apply (rule supp_comp_bound infinite_UNIV bij_comp | assumption)+
      done


     apply (rule allI impI)+
    subgoal for a z x t' g
      apply (rule fresh_cases[of "inv g ` imsupp f \<union> imsupp f" t'])
       apply (rule ordLeq_ordLess_trans[OF card_of_image] infinite_class.Un_bound iffD2[OF imsupp_supp_bound] infinite_UNIV assms)+
      apply (unfold Int_Un_distrib Un_empty)
      apply (erule conjE)+
      apply hypsubst_thin
      apply (subst (asm) vvsubst_ctor)
        apply (rule assms)
       apply assumption
      apply (rotate_tac -4)
      apply (unfold permute_simps)
      apply (drule sym)
      apply (drule TT_fresh_inject[THEN iffD1, of "imsupp f", rotated -1])
       apply (rule iffD2[OF imsupp_supp_bound])
       apply (rule infinite_UNIV)
         apply (rule assms)
        apply (subst term_pre.set_map, (rule assms supp_id_bound bij_id | assumption)+)+
       apply (unfold image_id)
       apply (rule iffD2[OF image_Int_empty_inv])
        apply assumption+
      apply (erule exE conjE)+
      apply hypsubst_thin

      apply (subst (asm) term_pre.set_map, (rule assms supp_id_bound bij_id | assumption)+)+
      apply (unfold image_id)
      apply (unfold image_comp comp_assoc[symmetric])
      apply (erule imageE)
      apply hypsubst_thin
      apply (unfold0 comp_apply)
      apply (erule allE)+
      apply (erule impE)
       prefer 2
       apply (erule impE)
        prefer 2
        apply (erule impE)
         apply (rule refl)
        apply (subst (asm) image_in_bij_eq[symmetric])
          apply assumption+
        apply (unfold image_comp)
        apply (erule imageE)
        apply hypsubst_thin
        apply (unfold0 comp_apply)
         apply (subst (asm) FVars_permutes)
           apply (rule bij_comp assms supp_comp_bound infinite_UNIV | assumption)+
      apply (subst (asm) image_in_bij_eq)
          apply (rule bij_comp assms supp_comp_bound infinite_UNIV | assumption)+
         apply (unfold0 o_inv_distrib comp_apply inv_simp1)
        apply (rule imageI)
        apply (erule FVars_intros)
      apply assumption+
      done
    done
  done

mrbnf "'a term"
  map: vvsubst
  sets:
    free: FVars_term
  bd: "card_suc natLeq"
         apply (rule vvsubst_id)
        apply (rule vvsubst_comp0[symmetric]; assumption)
       apply (rule vvsubst_cong0; assumption)
  subgoal for f
    apply (rule ext)
    apply (unfold comp_def)
    apply (rule FVars_vvsubst; assumption)
    done
     apply (rule infinite_regular_card_order_card_suc natLeq_card_order natLeq_Cinfinite)+
    apply (rule FVars_bds)
   apply (rule le_funI)+
   apply (unfold relcompp_apply)
   apply (rule le_boolI)
   apply (erule exE conjE)+
  apply (unfold vvsubst_id id_apply)
   apply hypsubst
   apply (rule exI conjI UNIV_I refl)+

  apply (rule iffI)
   apply (erule exE conjE)+
   apply hypsubst
   apply (rule exI conjI UNIV_I refl)+
  apply (erule exE conjE)+
  apply hypsubst
  apply (rule refl)
  done
print_theorems

end