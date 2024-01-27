theory ILC_Head_Reduction
imports ILC_uniform
begin 

(* Head reduction in the infinitary calculus: *)

definition hred :: "ivar iterm \<Rightarrow> ivar iterm \<Rightarrow> bool" where 
"hred e e' \<equiv> \<exists> xs e1 es2. e = iApp (iLam xs e1) es2 \<and> e' = itvsubst (imkSubst xs es2) e1"

lemma hred_irrename: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> hred e e' \<Longrightarrow> hred (irrename \<sigma> e) (irrename \<sigma> e')"
unfolding hred_def apply(elim exE) subgoal for xs e1 es2
  apply(rule exI[of _ "dsmap \<sigma> xs"])
  apply(rule exI[of _ "irrename \<sigma> e1"])  
  apply(rule exI[of _ "smap (irrename \<sigma>) es2"])   
  apply (simp add: iterm.rrename_comps) apply(subst irrename_itvsubst_comp) apply auto
  apply(subst imkSubst_smap_irrename_inv) unfolding ssbij_def apply auto 
  apply(subst irrename_eq_itvsubst_iVar'[of _ e1]) unfolding ssbij_def apply auto
  apply(subst itvsubst_comp) 
    subgoal by (metis SSupp_imkSubst imkSubst_smap_irrename_inv)
    subgoal by (smt (verit, best) SSupp_def VVr_eq_Var card_of_subset_bound mem_Collect_eq not_in_supp_alt o_apply subsetI) 
    subgoal apply(rule itvsubst_cong)
      subgoal using SSupp_irrename_bound by blast
      subgoal using card_SSupp_itvsubst_imkSubst_irrename_inv ssbij_def by auto
   subgoal for x apply simp apply(subst iterm.subst(1))
      subgoal using card_SSupp_imkSubst_irrename_inv[unfolded ssbij_def] by auto
      subgoal by simp . . . .

lemma hred_reneqv: 
assumes "reneqv e ee" "hred e e'" "hred ee ee'" 
shows "reneqv e' ee'"
using assms reneqv_head_reduction unfolding hred_def by auto 

lemma hred_reneqvS: 
assumes "reneqvS es ees" "stream_all2 hred es es'" and "stream_all2 hred ees ees'"
shows "reneqvS es' ees'"
using hred_reneqv assms unfolding reneqvS_def stream_all2_iff_snth sset_range  
by simp (smt (verit) image_iff)

lemma hred_uniform: 
assumes "hred e e'" and "uniform e"
shows "uniform e'"
using assms hred_reneqv unfolding uniform_def3 by blast

lemma hred_uniformS: 
assumes "stream_all2 hred es es'" and "uniformS es"
shows "uniformS es'"
using assms hred_reneqvS unfolding uniformS_def3 by blast

(* Other properties: *)

(* The following captures the freshness assumption for beta (coming from the "parameter" 
predicate hred as part of ustepD. So fresh induction will use both 
the avoidance from the ustepD Xi rule and this one (for hred).  Contrast this with 
beta, which does not "hide" any freshness assumptions inside parameter predicates, 
so its rule induction covers both beta and Xi. *)
lemma hred_eq_avoid: 
assumes A: "small A" and r: "hred e e'"
shows "\<exists> xs e1 es2. dsset xs \<inter> \<Union> (FFVars ` (sset es2)) = {} \<and> dsset xs \<inter> A = {} \<and>
            e = iApp (iLam xs e1) es2 \<and> e' = itvsubst (imkSubst xs es2) e1"
proof-
  obtain xs e1 es2 where e: "e = iApp (iLam xs e1) es2" and e': "e' = itvsubst (imkSubst xs es2) e1" 
  using r unfolding hred_def by auto
  define B where B: "B = A \<union> \<Union> (FFVars ` (sset es2))"
  have "small B" unfolding B
  apply(rule small_Un)
    subgoal by fact
    subgoal apply(rule small_UN)
      subgoal by (simp add: countable_card_ivar countable_sset)
      subgoal by (simp add: ILC2.small_def iterm.set_bd_UNIV) . .
  then obtain xs' e1' where 0: "iLam xs e1 = iLam xs' e1'" "dsset xs' \<inter> B = {}"
  using iLam_avoid by (meson small_def)

  obtain f where f: "bij f" "|supp f| <o |UNIV::ivar set|" "id_on (FFVars (iLam xs e1)) f" 
  and 1: "xs' = dsmap f xs" "e1' = irrename f e1" using 0(1) unfolding iLam_inject by auto
  show ?thesis apply(intro exI[of _ xs'] exI[of _ e1'] exI[of _ es2]) apply(intro conjI)
    subgoal using 0(2) unfolding B by auto
    subgoal using 0(2) unfolding B by auto
    subgoal unfolding e 0(1) ..
    subgoal unfolding e' 0(1) 1 apply(subst irrename_eq_itvsubst_iVar')
      subgoal by fact  subgoal by fact
      subgoal apply(subst itvsubst_comp)
        subgoal by simp
        subgoal by (simp add: f(2))   
        apply(subst itvsubst_cong) apply auto 
        apply (simp add: SSupp_itvsubst_bound f(2))
        by (metis (full_types) "0"(1) "1"(1) Diff_iff f(1) f(3) id_on_def imkSubst_idle 
          imkSubst_smap iterm.set(3)) . . 
qed

lemma hred_FFVars: "hred e e' \<Longrightarrow> FFVars e' \<subseteq> FFVars e"
unfolding hred_def by auto (metis imkSubst_def iterm.set(1) singletonD snth_sset)+

lemma hred_determ: 
"hred e e' \<Longrightarrow> hred e e'' \<Longrightarrow> e' = e''"
unfolding hred_def  
by auto (meson iLam_eq_imkSubst)



end