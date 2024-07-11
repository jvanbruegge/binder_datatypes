(* Here we instantiate the general enhanced rule induction to beta reduction
for Mazza's infinitary lambda-calculus *)
theory ILC_Beta 
imports ILC2 "Prelim.Curry_LFP" 
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

type_synonym T = "itrm \<times> itrm"

definition Tperm :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tperm f \<equiv> map_prod (irrename f) (irrename f)"

fun Tsupp :: "T \<Rightarrow> ivar set" where 
"Tsupp (e1,e2) = FFVars e1 \<union> FFVars e2"

lemma small_Tsupp: "small (Tsupp t)"
  unfolding small_def
  by (cases t) (auto intro!: var_iterm_pre_class.Un_bound iterm.card_of_FFVars_bounds)

lemma Tvars_dsset: "(Tsupp t - dsset xs) \<inter> dsset xs = {}" "|Tsupp t - dsset xs| <o |UNIV::ivar set|"
apply auto by (meson card_of_minus_bound small_Tsupp small_def)

binder_inductive istep :: "itrm \<Rightarrow> itrm \<Rightarrow> bool" where
  Beta: "istep (iApp (iLam xs e1) es2) (itvsubst (imkSubst xs es2) e1)" binds "dsset xs"
| iAppL: "istep e1 e1' \<Longrightarrow> istep (iApp e1 es2) (iApp e1' es2)"
| iAppR: "istep (snth es2 i) e2' \<Longrightarrow> istep (iApp e1 es2) (iApp e1 (supd es2 i e2'))"
| Xi: "istep e e' \<Longrightarrow> istep (iLam xs e) (iLam xs e')" binds "dsset xs"
where perm: Tperm supp: Tsupp
  unfolding isPerm_def Tperm_def  
  using small_Un small_def iterm.card_of_FFVars_bounds
         apply (auto simp: iterm.rrename_id0s map_prod.comp iterm.rrename_comp0s infinite_UNIV) [5]
  using var_sum_class.Un_bound unfolding small_def apply blast
  subgoal by fastforce
  subgoal for \<sigma> R B t
    unfolding split_beta
    apply(elim disjE)
    subgoal apply(rule disjI4_1)
      subgoal apply(elim exE) subgoal for xs e1 es2
        apply(rule exI[of _ "dsmap \<sigma> xs"])
        apply(rule exI[of _ "irrename \<sigma> e1"])  
        apply(rule exI[of _ "smap (irrename \<sigma>) es2"])  
        apply(cases t) unfolding isPerm_def small_def Tperm_def 
        apply (simp add: iterm.rrename_comps) apply(subst irrename_itvsubst_comp) apply auto
        apply(subst imkSubst_smap_irrename_inv) unfolding isPerm_def apply auto 
        apply(subst irrename_eq_itvsubst_iVar'[of _ e1]) unfolding isPerm_def apply auto
        apply(subst itvsubst_comp) 
        subgoal by (metis SSupp_imkSubst imkSubst_smap_irrename_inv)
        subgoal by (smt (verit, best) SSupp_def VVr_eq_Var card_of_subset_bound mem_Collect_eq not_in_supp_alt o_apply subsetI) 
        subgoal apply(rule itvsubst_cong)
          subgoal using SSupp_irrename_bound by blast
          subgoal using card_SSupp_itvsubst_imkSubst_irrename_inv isPerm_def by auto
          subgoal for x apply simp apply(subst iterm.subst(1))
            subgoal using card_SSupp_imkSubst_irrename_inv[unfolded isPerm_def] by auto
            subgoal by simp . . . . . 
      (* *)
  subgoal apply(rule disjI4_2)
    subgoal apply(elim exE) subgoal for e1 e1' es2 
      apply(rule exI[of _ "irrename \<sigma> e1"]) apply(rule exI[of _ "irrename \<sigma> e1'"]) 
      apply(rule exI[of _ "smap (irrename \<sigma>) es2"]) 
      apply(cases t) unfolding isPerm_def small_def Tperm_def 
      by (simp add: iterm.rrename_comps) . . 
    (* *)
  subgoal apply(rule disjI4_3)
    subgoal apply(elim exE) subgoal for es2 i e2' e1 
      apply(rule exI[of _ "smap (irrename \<sigma>) es2"]) 
      apply(rule exI[of _ i])
      apply(rule exI[of _ "irrename \<sigma> e2'"]) 
      apply(rule exI[of _ "irrename \<sigma> e1"])
      apply(cases t) unfolding isPerm_def small_def Tperm_def 
      apply (simp add: iterm.rrename_comps) . . .
    (* *)
  subgoal apply(rule disjI4_4)
    subgoal apply(elim exE) subgoal for e e' xs
      apply(rule exI[of _ "irrename \<sigma> e"]) apply(rule exI[of _ "irrename \<sigma> e'"]) 
      apply(rule exI[of _ "dsmap \<sigma> xs"])
      apply(cases t) unfolding isPerm_def small_def Tperm_def  
      by (simp add: iterm.rrename_comps) . . . 
  subgoal premises prems for R B t
    using prems(2-)
    unfolding Tperm_def split_beta apply safe
    subgoal for xs e1 es2  
      using refresh[OF Tvars_dsset, of xs t]  apply safe
      subgoal for f
        apply(rule exI[of _ "f ` (dsset xs)"])  
        apply(intro conjI)
        subgoal by (metis dsset_card_ls dstream.set_map)
        subgoal unfolding id_on_def by auto (metis DiffI Int_emptyD image_eqI)
        subgoal apply(rule disjI4_1)
          apply(rule exI[of _ "dsmap f xs"]) 
          apply(rule exI[of _ "irrename f e1"]) 
          apply(rule exI[of _ "es2"]) 
          apply(cases t)  apply simp apply(intro conjI)
          subgoal apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
          subgoal apply(subst irrename_eq_itvsubst_iVar)
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
                subgoal unfolding isPerm_def small_def by auto 
                subgoal apply(rule disjI4_2) 
                  apply(rule exI[of _ "e1"]) 
                  apply(rule exI[of _ "e1'"])
                  apply(rule exI[of _ "es2"]) 
                  apply(cases t) apply simp . .
                  (* *)
              subgoal for e1 e2 es2' 
                apply(rule exI[of _ "{}"])  
                apply(intro conjI)
                subgoal by simp
                subgoal unfolding isPerm_def small_def by auto 
                subgoal apply(rule disjI4_3) 
                  apply(rule exI[of _ "e1"]) 
                  apply(rule exI[of _ "e2"])
                  apply(rule exI[of _ "es2'"]) 
                  apply(cases t) apply auto . .
                  (* *) 
              subgoal for e e' xs
                using refresh[OF Tvars_dsset, of xs t]  apply safe
                subgoal for f
                  apply(rule exI[of _ "f ` (dsset xs)"])  
                  apply(intro conjI)
                  subgoal by (metis dsset_card_ls dstream.set_map)
                  subgoal unfolding id_on_def by auto (metis DiffI Int_emptyD image_eqI)
                  subgoal apply(rule disjI4_4)  
                    apply(rule exI[of _ "irrename f e"]) 
                    apply(rule exI[of _ "irrename f e'"]) 
                    apply(rule exI[of _ "dsmap f xs"])
                    apply(cases t)  apply simp apply(intro conjI)
                    subgoal apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
                    subgoal apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
                    . . . .
                  done

corollary strong_induct_istep[consumes 2, case_names Beta iAppL iAppR Xi]: 
assumes par: "\<And>p. small (Psupp p)"
and st: "istep t1 t2"  
and Beta: "\<And>xs e1 es2 p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> dsset xs \<inter> \<Union>(FFVars`(sset es2)) = {} \<Longrightarrow> 
  R p (iApp (iLam xs e1) es2) (itvsubst (imkSubst xs es2) e1)"
and iAppL: "\<And>e1 e1' es2 p. 
  istep e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  R p (iApp e1 es2) (iApp e1' es2)"
and iAppR: "\<And>e1 es2 i e2' p. 
  istep (snth es2 i) e2' \<Longrightarrow> (\<forall>p'. R p' (es2 !! i) e2') \<Longrightarrow> 
  R p (iApp e1 es2) (iApp e1 (supd es2 i e2'))"
and Xi: "\<And>e e' xs p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> 
  istep e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (iLam xs e) (iLam xs e')" 
shows "R p t1 t2"
unfolding istep.alt_def
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st apply(elim istep.strong_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding istep.alt_def by simp
    subgoal for p B t
    unfolding istep.alt_def[symmetric] apply(elim disjE exE case_prodE)
      subgoal for _ _ xs e1 es2 using Beta[of xs p es2 e1] by force
      subgoal using iAppL by auto  
      subgoal using iAppR by auto  
      subgoal using Xi by auto . . .

corollary strong_induct_istep''[consumes 1, case_names Bound Beta iAppL iAppR Xi]: 
assumes st: "istep t1 t2"
and par: "\<And>p. |Psupp p| <o |UNIV::ivar set|"
and Beta: "\<And>xs e1 es2 p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> dsset xs \<inter> \<Union>(FFVars`(sset es2)) = {} \<Longrightarrow> 
  R (iApp (iLam xs e1) es2) (itvsubst (imkSubst xs es2) e1) p"
and iAppL: "\<And>e1 e1' es2 p. 
  istep e1 e1' \<Longrightarrow> (\<forall>p'. R e1 e1' p') \<Longrightarrow> 
  R (iApp e1 es2) (iApp e1' es2) p"
and iAppR: "\<And>e1 es2 i e2' p. 
  istep (snth es2 i) e2' \<Longrightarrow> (\<forall>p'. R (es2 !! i) e2' p') \<Longrightarrow> 
  R (iApp e1 es2) (iApp e1 (supd es2 i e2')) p"
and Xi: "\<And>e e' xs p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> 
  istep e e' \<Longrightarrow> (\<forall>p'. R e e' p') \<Longrightarrow> 
  R (iLam xs e) (iLam xs e') p" 
shows "\<forall>p. (R t1 t2 p)"
using strong_induct_istep[of Psupp t1 t2 "\<lambda>p t1 t2. R t1 t2 p"] assms unfolding small_def by auto

(* Also inferring equivariance from the general infrastructure: *)
corollary irrename_istep:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" 
and r: "istep e e'" 
shows "istep (irrename f e) (irrename f e')"
using assms unfolding istep.alt_def using istep.equiv[of "(e,e')" f]
unfolding Tperm_def isPerm_def by auto

(* Other properties: *)

lemma SSupp_If_small[simp]: "|A :: ivar set| <o |UNIV :: ivar set| \<Longrightarrow>
  |SSupp (\<lambda>x. if x \<in> A then f x else iVar x)| <o |UNIV :: ivar set|"
  by (smt (verit, del_insts) SSupp_def VVr_eq_Var card_of_subset_bound mem_Collect_eq subsetI)

lemma istep_FFVars: "istep e e' \<Longrightarrow> ILC.FFVars e' \<subseteq> ILC.FFVars e"
  by(induct rule: istep.induct) (auto simp: imkSubst_def card_dsset_ivar)


 

end