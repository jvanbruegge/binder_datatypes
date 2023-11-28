(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory ILC_relations_more
imports (* ILC_uniform *) ILC_affine ILC_Beta ILC_UBeta
begin


(* TO DOCUMENT IN THE PAPER: 
An example where normal induction would not work, but fresh induction with empty parameters 
is helpful -- namely, the "bonus" freshness assumption allows us to assume xs fresh for es, 
which is crucial in the beta case. *)
lemma istep_affine:
assumes "istep e e'" and "affine e"
shows "affine e'"
proof-
  have "ILC2.small {}" by simp
  thus ?thesis using assms apply(induct rule: BE_induct_istep')
    subgoal for xs e1 es2 apply(rule imkSubst_affine)
    unfolding affine_iApp_iff by auto 
    subgoal unfolding affine_iApp_iff using istep_FFVars by fastforce
    subgoal unfolding affine_iApp_iff using istep_FFVars 
    by simp (smt (verit, ccfv_SIG) Int_subset_empty1 More_Stream.theN disjoint_iff snth_sset snth_supd_diff snth_supd_same)
    subgoal by auto . 
qed

definition "affineS es \<equiv> (\<forall>e\<in>sset es. affine e) \<and> (\<forall>i j. i \<noteq> j \<longrightarrow> ILC.FFVars (snth es i) \<inter> ILC.FFVars (snth es j) = {})"

lemma hread_affine: "hred e e' \<Longrightarrow> affine e \<Longrightarrow> affine e'"
using hred_def istep.Beta istep_affine by fastforce

lemma hred_affineS: 
"stream_all2 hred es es' \<Longrightarrow> affineS es \<Longrightarrow> affineS es'"
using hread_affine unfolding stream_all2_iff_snth affineS_def sset_range 
by auto (metis disjoint_iff_not_equal hred_def insert_absorb insert_subset istep.Beta istep_FFVars)

lemma affineS_smap2_iApp_iff: 
"affineS (smap2 iApp es ess) \<longleftrightarrow> 
 affineS es \<and> affineS (sflat ess) \<and> 
  (\<forall>i j k. ILC.FFVars (snth es i) \<inter> ILC.FFVars (snth2 ess (j,k)) = {})"
sorry

lemma affineS_sflat: "affineS (sflat ess) \<longleftrightarrow> 
 (\<forall>i j i' j'. affine (snth2 ess (i,j)) \<and> ILC.FFVars ((snth2 ess (i,j))) \<inter> ILC.FFVars ((snth2 ess (i',j'))) = {})"
sorry 

lemma affineS_smap_iLam_iff: "affineS (smap (iLam xs) es) \<longleftrightarrow> 
  (\<forall>i j. i \<noteq> j \<longrightarrow> affine (snth es i) \<and> ILC.FFVars (snth es i) \<inter> ILC.FFVars (snth es j) \<subseteq> dsset xs)"
unfolding affineS_def by auto (metis More_Stream.theN nat.simps(3))

lemma ustep_affine:
assumes "ustep es es'"
shows "\<forall>i. affine (es !! i) \<longrightarrow> affine (es' !! i)"
using assms apply(induct rule: ustep.induct)
  subgoal for es es' unfolding stream_all2_iff_snth using hread_affine by auto
  subgoal apply auto unfolding affine_iApp_iff using ustep_FFVars by fastforce
  subgoal apply auto unfolding affine_iApp_iff using ustep_FFVars 
  apply (auto simp: snth_sflat sset_range image_def)
    apply (metis nat2_nat1 snth2.simps) 
    apply (metis Int_emptyD in_mono nat2_nat1 snth2.simps snth_sflat)
    by (metis Int_emptyD insert_absorb insert_subset nat2_nat1 snth2.simps snth_sflat) 
  subgoal for es es' xs apply(frule ustep_FFVars) by auto  . 

lemma ustep_affineS:
assumes "ustep es es'" and "affineS es"
shows "affineS es'"
using assms ustep_affine ustep_FFVars unfolding affineS_def apply auto 
  apply (metis More_Stream.theN snth_sset)
  by (meson disjoint_iff_not_equal in_mono)



end 
