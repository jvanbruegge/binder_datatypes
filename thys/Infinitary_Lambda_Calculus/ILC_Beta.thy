(* Here we instantiate the general enhanced rule induction to beta reduction
for Mazza's infinitary lambda-calculus *)
theory ILC_Beta
imports ILC2 "Prelim.Curry_LFP"
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

abbreviation Tsupp :: "itrm \<Rightarrow> itrm \<Rightarrow> ivar set" where
"Tsupp e1 e2 \<equiv> iFV e1 \<union> iFV e2"

lemma small_Tsupp: "small (Tsupp t1 t2)"
  unfolding small_def
  by (auto intro!: var_iterm_pre_class.Un_bound iterm.set_bd_UNIV)

lemma Tvars_dsset: "(Tsupp t1 t2 - dsset xs) \<inter> dsset xs = {}" "|Tsupp t1 t2 - dsset xs| <o |UNIV::ivar set|"
apply auto by (meson card_of_minus_bound small_Tsupp small_def)

inductive istep :: "itrm \<Rightarrow> itrm \<Rightarrow> bool" where
  Beta: "istep (iAp (iLm xs e1) es2) (itvsubst (imkSubst xs es2) e1)"
| iAppL: "istep e1 e1' \<Longrightarrow> istep (iAp e1 es2) (iAp e1' es2)"
| iAppR: "istep (snth es2 i) e2' \<Longrightarrow> istep (iAp e1 es2) (iAp e1 (supd es2 i e2'))"
| Xi: "istep e e' \<Longrightarrow> istep (iLm xs e) (iLm xs e')"

lemmas [equiv] =
  iterm.tvsubst_permutes[THEN fun_cong, unfolded comp_def]
  imkSubst_smap_irrename[symmetric, THEN fun_cong, unfolded comp_def]

binder_inductive istep
  subgoal premises prems for R B x1 x2
    using prems(2-) apply safe
    subgoal for xs e1 es2
      using refresh[OF Tvars_dsset, of xs x1 x2]  apply safe
      subgoal for f
        apply(rule exI[of _ "f ` (dsset xs)"])
        apply(intro conjI)
        subgoal by (simp add: Diff_Int_distrib)
        subgoal apply(rule disjI4_1)
          apply(rule exI[of _ "dsmap f xs"])
          apply(rule exI[of _ "irrename f e1"])
          apply(rule exI[of _ "es2"])
          apply simp apply(intro conjI)
          subgoal apply(subst iLm_irrename[of "f"]) unfolding id_on_def by auto
          subgoal apply(subst irrename_eq_itvsubst_iVr)
            subgoal unfolding isPerm_def by auto
            subgoal unfolding isPerm_def by auto
            subgoal apply(subst itvsubst_comp)
              subgoal by auto
              subgoal by simp
              subgoal apply(rule itvsubst_cong)
                subgoal by blast
                subgoal by (simp add: SSupp_itvsubst_bound)
                subgoal unfolding id_on_def
                  by simp (metis (no_types, lifting) bij_not_eq_twice imageE imkSubst_idle imkSubst_smap dstream.set_map)
                . . . . . .
                  (* *)
              subgoal for e1 e1' es2
                apply(rule exI[of _ "{}"])
                apply(intro conjI)
                subgoal by simp
                subgoal by auto .
                  (* *)
              subgoal for e1 e2 es2'
                apply(rule exI[of _ "{}"])
                apply(intro conjI)
                subgoal by simp
                subgoal unfolding isPerm_def small_def by auto .
                  (* *)
              subgoal for e e' xs
                using refresh[OF Tvars_dsset, of xs x1 x2]  apply safe
                subgoal for f
                  apply(rule exI[of _ "f ` (dsset xs)"])
                  apply(intro conjI)
                  subgoal by (metis Diff_Int_distrib Diff_empty dstream.set_map)
                  subgoal apply(rule disjI4_4)
                    apply(rule exI[of _ "irrename f e"])
                    apply(rule exI[of _ "irrename f e'"])
                    apply(rule exI[of _ "dsmap f xs"])
                    apply simp apply(intro conjI)
                    subgoal apply(subst iLm_irrename[of "f"]) unfolding id_on_def by auto
                    subgoal apply(subst iLm_irrename[of "f"]) unfolding id_on_def by auto
                    . . . .
                  done

thm istep.strong_induct
thm istep.equiv

(* Other properties: *)

lemma SSupp_If_small[simp]: "|A :: ivar set| <o |UNIV :: ivar set| \<Longrightarrow>
  |SSupp (\<lambda>x. if x \<in> A then f x else iVr x)| <o |UNIV :: ivar set|"
  by (smt (verit, del_insts) SSupp_def VVr_eq_Var card_of_subset_bound mem_Collect_eq subsetI)

lemma istep_iFV: "istep e e' \<Longrightarrow> ILC.iFV e' \<subseteq> ILC.iFV e"
  by(induct rule: istep.induct) (auto simp: imkSubst_def card_dsset_ivar)




end