theory InfFOL imports InfFmla
begin

binder_inductive (no_auto_equiv, no_auto_refresh) deduct :: "fmla set\<^sub>k \<Rightarrow> fmla \<Rightarrow> bool" (infix "\<turnstile>" 100) where
  Hyp: "f \<in>\<^sub>k \<Delta> \<Longrightarrow> \<Delta> \<turnstile> f"
| ConjI: "(\<And>f. f \<in>\<^sub>k\<^sub>1 F \<Longrightarrow> \<Delta> \<turnstile> f) \<Longrightarrow> \<Delta> \<turnstile> Conj F"
| ConjE: "\<lbrakk> \<Delta> \<turnstile> Conj F ; f \<in>\<^sub>k\<^sub>1 F \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> f"
| NegI: "\<Delta>,f \<turnstile> \<bottom> \<Longrightarrow> \<Delta> \<turnstile> Neg f"
| NegE: "\<lbrakk> \<Delta> \<turnstile> Neg f ; \<Delta> \<turnstile> f \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<bottom>"
| AllI: "\<lbrakk> \<Delta> \<turnstile> f ; set\<^sub>k\<^sub>2 V \<inter> \<Union>(FFVars_fmlaP ` set\<^sub>k \<Delta>) = {} \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> All V f"
| AllE: "\<lbrakk> \<Delta> \<turnstile> All V f ; supp \<rho> \<subseteq> set\<^sub>k\<^sub>2 V \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> f\<lbrakk>\<rho>\<rbrakk>"
  subgoal for R B \<sigma> x1 x2
    unfolding induct_rulify_fallback split_beta
    apply (elim disj_forward exE)
          apply (auto simp: fmlaP.rrename_comps in_k_equiv in_k_equiv' isPerm_def fmlaP.rrename_ids supp_inv_bound)
         apply (rule exI)
         apply (rule conjI)
          apply (rule refl)
         apply (rule allI impI)+
         apply (unfold set\<^sub>k.map_comp)
         apply (subst fmlaP.rrename_comp0s)
             apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
         apply (subst inv_o_simp1, assumption)
         apply (unfold fmlaP.rrename_id0s set\<^sub>k.map_id)
         apply (rotate_tac -1)
         apply (drule iffD2[OF in_k1_equiv, of "inv \<sigma>", rotated])
          apply (unfold isPerm_def)
          apply (assumption | rule conjI bij_imp_bij_inv supp_inv_bound)+
         apply (subst (asm) set\<^sub>k\<^sub>1.map_comp)
         apply (subst (asm) fmlaP.rrename_comp0s)
             apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
         apply (subst (asm) inv_o_simp1, assumption)
         apply (unfold fmlaP.rrename_id0s set\<^sub>k\<^sub>1.map_id)
         apply (erule allE)
         apply (erule impE)
          apply assumption+
        apply (subst fmlaP.rrename_comp0s)
            apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
        apply (subst inv_o_simp1, assumption)
        apply (unfold fmlaP.rrename_id0s set\<^sub>k.map_id)
        apply (metis bij_imp_bij_inv fmlaP.rrename_comps fmlaP.rrename_ids fmlaP_rrename_simps(3) in_k1_equiv' inv_o_simp1 supp_inv_bound)
       apply (metis fmlaP.rrename_bijs fmlaP.rrename_inv_simps inv_o_simp1 inv_simp1 set\<^sub>k.map_id)
      apply (metis fmlaP.rrename_bijs fmlaP.rrename_inv_simps inv_o_simp1 inv_simp1 set\<^sub>k.map_id)
    subgoal for f V
      apply (rule exI[of _ "rrename_fmlaP \<sigma> f"])
      apply (rule exI[of _ "map_set\<^sub>k\<^sub>2 \<sigma> V"])
      by (smt (verit, ccfv_threshold) bij_imp_bij_inv fmlaP.rrename_comp0s fmlaP.rrename_id0s fmlaP.rrename_ids fmlaP.set_map0 fmlaP_vvsubst_rrename image_Int_empty image_Union image_comp inv_o_simp1 pointfree_idE set\<^sub>k.map_ident_strong set\<^sub>k.set_map set\<^sub>k\<^sub>2.set_map supp_inv_bound)
    subgoal for V f \<rho>
      apply (rule exI[of _ "map_set\<^sub>k\<^sub>2 \<sigma> V"])
      apply (unfold set\<^sub>k\<^sub>2.set_map)
      apply (rule conjI)
       apply (rule refl)
      apply (unfold set\<^sub>k\<^sub>2.map_comp)
      apply (subst inv_o_simp1, assumption)
      apply (unfold set\<^sub>k\<^sub>2.map_id)
      apply (rule exI[of _ "rrename_fmlaP \<sigma> f"])
      apply (subst fmlaP.rrename_comps)
          apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
      apply (subst inv_o_simp1, assumption)
      apply (unfold fmlaP.rrename_ids)
      apply (rule exI[of _ "\<sigma> \<circ> \<rho> \<circ> inv \<sigma>"])
      apply (subgoal_tac "|supp \<rho>| <o |UNIV::k set|")
       prefer 2
       apply (erule card_of_subset_bound)
      apply (simp add: small_set\<^sub>k\<^sub>2[unfolded small_def])
      apply (subst fmlaP.map_comp0)
        apply (rule supp_inv_bound supp_comp_bound infinite_UNIV | assumption)+
      apply (subst fmlaP.map_comp0)
        apply (rule supp_inv_bound supp_comp_bound infinite_UNIV | assumption)+
      apply (subst supp_o_bij)
       apply assumption
      apply (subst comp_apply)
      apply (unfold fmlaP_vvsubst_rrename fmlaP_vvsubst_rrename[OF bij_imp_bij_inv supp_inv_bound])
      apply (subst fmlaP.rrename_comps)
          apply (rule supp_inv_bound bij_imp_bij_inv | assumption)+
      apply (subst inv_o_simp1, assumption)
      apply (unfold fmlaP.rrename_ids comp_def)
      apply (rule conjI)
       apply (rule refl)
      apply (rule conjI)
      apply (metis fmlaP.rrename_bijs fmlaP.rrename_inv_simps inv_simp1 set\<^sub>k.map_ident_strong)
      apply (erule image_mono)
      done
    done
  subgoal premises prems for R B \<Delta> x2
    using prems(2-) unfolding induct_rulify_fallback split_beta
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
    apply (elim disj_forward)
          apply auto[5]
     apply (elim exE conjE)
    apply simp
    subgoal for \<Delta> f V
      apply (rule exE[OF refresh[of V "\<Union>(FFVars_fmlaP ` set\<^sub>k \<Delta>) \<union> FFVars_fmlaP (All V f)", unfolded fmlaP.set
              Un_Diff Diff_idemp
              ]])
        apply blast
      apply (metis (no_types, lifting) fmlaP.set(4) fmlaP.set_bd_UNIV set\<^sub>k.set_bd var_fmlaP_pre_class.UN_bound var_fmlaP_pre_class.Un_bound)
      apply (erule exE conjE)+
      subgoal for g VV
        apply (rule exI[of _ "map_set\<^sub>k (rrename_fmlaP g) \<Delta>"])
        apply (rule exI[of _ "g ` set\<^sub>k\<^sub>2 V"])
        apply (rule conjI[rotated])
         apply (metis set\<^sub>k\<^sub>2.set_map)
        apply (rule exI[of _ "rrename_fmlaP g f"])
        apply (rule exI[of _ VV])
        apply (rule conjI)
         apply (drule arg_cong[of _ _ set\<^sub>k\<^sub>2])
         apply (unfold set\<^sub>k\<^sub>2.set_map)
         apply assumption
        apply (rule conjI)
         apply (rule trans)
          apply (rule set\<^sub>k.map_id[symmetric])
         apply (rule set\<^sub>k.map_cong)
          apply (rule refl)
         apply (rule trans)
          apply (rule id_apply)
         apply (rule sym)
         apply (rule fmlaP.rrename_cong_ids)
           apply assumption+
         apply (erule id_onD)
         apply (rule UnI1)
         apply blast
        apply (rule conjI[rotated])
         apply (rule conjI)
          apply (drule meta_spec)+
          apply (drule meta_mp)
           prefer 2
           apply assumption
          apply (rule conjI | assumption)+

         apply (unfold set\<^sub>k.set_map image_comp[unfolded comp_def] fmlaP.FFVars_rrenames
            image_UN[symmetric]
            )[1]
         apply hypsubst
         apply (unfold set\<^sub>k\<^sub>2.set_map)
         apply (rule trans)
          apply (rule image_Int[symmetric])
          apply (erule bij_is_inj)
         apply (rule iffD2[OF image_is_empty])
         apply assumption

        apply (subst All_def)+
        apply (unfold fmlaP.TT_injects0)
        apply (rule exI[of _ g])
        apply (rule conjI, assumption)+
        apply (rule conjI)

         apply (unfold set3_fmlaP_pre_def comp_def Abs_fmlaP_pre_inverse[OF UNIV_I]
            map_sum.simps map_prod_simp sum_set_simps prod_set_simps Un_empty cSup_singleton
            Un_empty_left Un_empty_right Union_empty UN_single set2_fmlaP_pre_def set\<^sub>k\<^sub>2.set_map
            UN_singleton map_fmlaP_pre_def
            )
         apply (erule id_on_antimono)
         apply (rule Un_upper2)
        apply hypsubst
        apply (rule refl)
        done
      done

     apply (elim exE conjE)
    apply simp
    apply hypsubst_thin
    apply (subst fmlaP.set_map)
    apply (meson card_of_subset_bound small_def small_set\<^sub>k\<^sub>2)
    apply (unfold triv_forall_equality)

    subgoal premises prems for V f \<rho>
    proof -
      define X where "X \<equiv> set\<^sub>k\<^sub>2 V"
      let ?O = "\<Union> (FFVars_fmlaP ` set\<^sub>k \<Delta>) \<union> \<rho> ` FFVars_fmlaP f \<union> imsupp \<rho> \<union> X \<union> (FFVars_fmlaP f - set\<^sub>k\<^sub>2 V)"
      have osmall: "|?O| <o |UNIV::var set|"
        apply (intro var_fmlaP_pre_class.Un_bound)
        apply (meson fmlaP.set_bd_UNIV set\<^sub>k.set_bd var_fmlaP_pre_class.UN_bound)
        using fmlaP.set_bd_UNIV small_def small_image apply blast
        unfolding imsupp_def
        apply (meson card_of_image card_of_subset_bound ordLeq_ordLess_trans prems(3) small_def small_set\<^sub>k\<^sub>2 var_fmlaP_pre_class.Un_bound)
        using X_def small_def small_set\<^sub>k\<^sub>2 apply blast
        using card_of_minus_bound fmlaP.set_bd_UNIV by blast

      obtain W' g where W': "W' \<inter> ?O = {}" "bij_betw g X W'"
      proof atomize_elim
        have "|UNIV - ?O| =o |UNIV::var set|" apply(rule card_of_Un_diff_infinite) apply (rule infinite_UNIV)
          by (rule osmall)
        then have "|X| <o |UNIV - ?O|"
          using X_def ordIso_iff_ordLeq ordLess_ordLeq_trans small_def small_set\<^sub>k\<^sub>2 by blast
        then obtain g where "inj_on g X" "g ` X \<subseteq> UNIV - ?O"
          by (meson card_of_ordLeq ordLess_imp_ordLeq)
        then show "\<exists>W' g. W' \<inter> ?O = {} \<and> bij_betw g X W'"
          apply -
          apply (rule exI[of _ "g ` X"])
          by (meson Diff_disjoint bij_betw_inv disjoint_iff in_mono inj_on_imp_bij_betw)
      qed

      define \<sigma> where "\<sigma> \<equiv> \<lambda>x. if x \<in> X then g x else if x \<in> W' then inv_into X g x else x"

      have \<sigma>: "\<forall>x\<in>(X \<union> W'). \<sigma> (\<sigma> x) = x" "id_on (-(X \<union> W')) \<sigma>"
        unfolding \<sigma>_def
        using W' apply auto apply (auto simp: bij_betw_inv_into_left bij_betw_apply bij_betw_imp_surj_on inv_into_into)
         apply (simp add: bij_betw_def f_inv_into_f)
        by (simp add: id_on_def)

      then have \<sigma>_involuntory[simp]:"\<And>x. \<sigma> (\<sigma> x) = x" by (metis Un_iff \<sigma>_def)

      then have \<sigma>_bij: "bij \<sigma>" using involuntory_imp_bij by blast
      have \<sigma>_inv: "inv \<sigma> = \<sigma>" by (simp add: inv_equality)

      have "|X \<union> W'| <o |UNIV::var set|" unfolding X_def using W'
        using small_set\<^sub>k\<^sub>2[unfolded small_def]
        by (metis X_def bij_betw_imp_surj_on small_def small_image var_fmlaP_pre_class.Un_bound)
      moreover have "supp \<sigma> \<subseteq> X \<union> W'" using \<sigma>(2) unfolding id_on_def by (meson UnI1 UnI2 \<sigma>_def not_in_supp_alt subsetI)
      ultimately have \<sigma>_small: "|supp \<sigma>| <o |UNIV::var set|" using card_of_subset_bound by blast

      define \<rho>' where "\<rho>' \<equiv> \<lambda>x. if x \<in> \<sigma> ` FFVars_fmlaP f then (\<rho> \<circ> \<sigma>) x else x"
      have "supp \<rho>' \<subseteq> supp (\<rho> \<circ> \<sigma>)" unfolding \<rho>'_def supp_def by auto
      then have \<rho>'_small: "|supp \<rho>'| <o |UNIV::var set|"
        by (meson \<sigma>_small card_of_subset_bound fmlaP_pre.supp_comp_bound prems(3) small_def small_set\<^sub>k\<^sub>2)

      show ?thesis using prems W'
        apply -
        apply (rule exI[of _ "\<Delta>"])
        apply (rule exI[of _ "\<sigma> ` set\<^sub>k\<^sub>2 V"])
        apply (rule conjI)
         apply (rule exI[of _ "map_set\<^sub>k\<^sub>2 \<sigma> V"])
         apply (rule conjI[rotated])+
           apply (rule exI[of _ "rrename_fmlaP \<sigma> f"])
           apply (rule exI[of _ \<rho>'])

           apply (rule conjI)
            apply (subst fmlaP_vvsubst_rrename[symmetric])
              apply (rule \<sigma>_bij)
             apply (rule \<sigma>_small)
            apply (subst fmlaP.map_comp)
              apply (rule \<sigma>_small)
             apply (rule \<rho>'_small)
            apply (rule fmlaP.map_cong)
               apply (meson card_of_subset_bound small_def small_set\<^sub>k\<^sub>2)
              apply (rule supp_comp_bound)
                apply (rule \<sigma>_small)
               apply (rule \<rho>'_small)
              apply (rule infinite_UNIV)
             apply (rule refl)
            apply (unfold \<rho>'_def comp_def)[1]
            apply simp

           apply (rule conjI)
            apply (rule iffD2[OF arg_cong[of _ _ "R _"]])
             prefer 2
             apply assumption
            apply (rule sym)
            apply (unfold All_def fmlaP.TT_injects0)[1]
            apply (unfold set3_fmlaP_pre_def comp_def Abs_fmlaP_pre_inverse[OF UNIV_I]
            map_sum.simps map_prod_simp sum_set_simps prod_set_simps Un_empty cSup_singleton
            Un_empty_left Un_empty_right Union_empty UN_single set2_fmlaP_pre_def set\<^sub>k\<^sub>2.set_map
            UN_singleton map_fmlaP_pre_def
            )[1]
            apply (rule exI[of _ \<sigma>])
            apply (rule conjI, rule \<sigma>_bij)
            apply (rule conjI, rule \<sigma>_small)
            apply (rule conjI)
             apply (rule id_on_antimono[OF \<sigma>(2)])
        using W' X_def apply blast
            apply (rule refl)

           apply (unfold set\<^sub>k\<^sub>2.set_map)
           apply (subgoal_tac "supp (\<rho> \<circ> \<sigma>) \<inter> \<sigma> ` FFVars_fmlaP f \<subseteq> \<sigma> ` set\<^sub>k\<^sub>2 V")
            apply (smt (verit, best) IntI \<rho>'_def not_in_supp_alt subset_iff)
           apply (unfold supp_def imsupp_def)
        using X_def \<sigma>_def apply auto[1]
          apply (rule refl)
         apply (rule refl)
        by (smt (verit) Int_iff Un_Int_eq(1) X_def \<sigma>_def bij_betw_apply disjoint_iff image_iff)
    qed
    done
  done

thm deduct.strong_induct
thm deduct.equiv

end
