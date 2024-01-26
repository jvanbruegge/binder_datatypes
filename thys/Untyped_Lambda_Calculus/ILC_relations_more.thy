(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory ILC_relations_more
imports (* ILC_uniform *) ILC_affine ILC_Beta ILC_UBeta_depth
begin


(* An example where fresh induction with empty parameters allow one to use a weaker lemma -- 
namely, the "bonus" freshness assumption allows us to assume xs fresh for es, 
which is helpful in the beta case. *)


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

(* alternative proof by normal induction, using stronger lemma: *)
lemma 
assumes "istep e e'" and "affine e"
shows "affine e'"
using assms apply(induct rule: istep.induct)
  subgoal for xs e1 es2 apply(rule imkSubst_affine_strong) 
    subgoal by (simp add: affine_iApp_iff) 
    subgoal using affine_iApp_iff by auto
    subgoal using affine_iApp_iff by auto .
  subgoal unfolding affine_iApp_iff using istep_FFVars by fastforce
    subgoal unfolding affine_iApp_iff using istep_FFVars 
    by simp (smt (verit, ccfv_SIG) Int_subset_empty1 More_Stream.theN disjoint_iff snth_sset snth_supd_diff snth_supd_same)
    subgoal by auto . 


definition "affineS es \<equiv> (\<forall>e\<in>sset es. affine e) \<and> (\<forall>i j. i \<noteq> j \<longrightarrow> ILC.FFVars (snth es i) \<inter> ILC.FFVars (snth es j) = {})"

lemma hread_affine: "hred e e' \<Longrightarrow> affine e \<Longrightarrow> affine e'"
using hred_def istep.Beta istep_affine by fastforce

lemma hred_affineS: 
"stream_all2 hred es es' \<Longrightarrow> affineS es \<Longrightarrow> affineS es'"
using hread_affine unfolding stream_all2_iff_snth affineS_def sset_range 
by auto (metis disjoint_iff_not_equal hred_def insert_absorb insert_subset istep.Beta istep_FFVars)


lemma affineS_sflat: "affineS (sflat ess) \<longleftrightarrow> 
 (\<forall>i j i' j'. affine (snth2 ess (i,j)) \<and> 
    ((i,j) \<noteq> (i',j') \<longrightarrow> ILC.FFVars ((snth2 ess (i,j))) \<inter> ILC.FFVars ((snth2 ess (i',j'))) = {}))"
unfolding affineS_def sset_sflat sset_range image_def snth_sflat apply safe
  subgoal by (smt (verit, ccfv_threshold) UNIV_I mem_Collect_eq nat2_nat1 snth_sflat)
  subgoal apply auto by (metis Int_emptyD nat2_nat1 snth2.simps snth_sflat snth_supd_diff snth_supd_same)
  subgoal for i j i' j' x apply(erule allE[of _ "nat1 (i,j)"]) apply(erule allE[of _ "nat1 (i',j')"]) by auto
  subgoal by (metis snth2.elims)
  subgoal by (metis (no_types, lifting) Int_emptyD nat2_inj snth2.elims) .


lemma affineS_smap2_iApp_iff: 
"affineS (smap2 iApp es ess) \<longleftrightarrow> 
 affineS es \<and> affineS (sflat ess) \<and> 
  (\<forall>i j k. ILC.FFVars (snth es i) \<inter> ILC.FFVars (snth2 ess (j,k)) = {})"
unfolding affineS_def sset_sflat sset_range image_def snth_sflat affineS_sflat Un_def Int_def apply safe
  subgoal using affine_iApp_iff by fastforce
  subgoal by auto
  subgoal by auto (metis affine_iApp_iff snth2.elims snth_sset)
  subgoal for ii jj x apply(cases "nat2 ii", cases "nat2 jj") apply auto  
  by (metis Int_emptyD affine_iApp_iff nat2_inj snth_sset)
  subgoal by auto (metis Int_emptyD affine_iApp_iff snth_sset)
  subgoal apply(auto simp: affine_iApp_iff sset_range image_def)  
    apply (metis nat2_nat1 snth2.simps)
    by (metis nat2_nat1 prod.inject snth2.simps)
  subgoal apply auto
    apply (metis More_Stream.theN) 
    apply (metis More_Stream.theN) 
    by (smt (verit, ccfv_SIG) More_Stream.theN nat2_nat1 prod.inject snth2.simps) .


lemma affineS_smap_iLam_iff: "affineS (smap (iLam xs) es) \<longleftrightarrow> 
  (\<forall>i j. i \<noteq> j \<longrightarrow> affine (snth es i) \<and> ILC.FFVars (snth es i) \<inter> ILC.FFVars (snth es j) \<subseteq> dsset xs)"
unfolding affineS_def by auto (metis More_Stream.theN nat.simps(3))

(* *)

lemma ustepD_affine:
assumes "ustepD d es es'"
shows "\<forall>i. affine (es !! i) \<longrightarrow> affine (es' !! i)"
using assms apply(induct rule: ustepD.induct)
  subgoal for es es' unfolding stream_all2_iff_snth using hread_affine by auto
  subgoal apply auto unfolding affine_iApp_iff using ustepD_FFVars by fastforce
  subgoal apply auto unfolding affine_iApp_iff using ustepD_FFVars 
  apply (auto simp: snth_sflat sset_range image_def)
    apply (metis nat2_nat1 snth2.simps) 
    apply (metis Int_emptyD in_mono nat2_nat1 snth2.simps snth_sflat)
    by (metis Int_emptyD insert_absorb insert_subset nat2_nat1 snth2.simps snth_sflat) 
  subgoal for es es' xs apply(frule ustepD_FFVars) by auto  . 

lemma ustepD_affineS:
assumes "ustepD d es es'" and "affineS es"
shows "affineS es'"
using assms ustepD_affine ustepD_FFVars unfolding affineS_def apply auto 
  apply (metis More_Stream.theN snth_sset)
  by (meson disjoint_iff_not_equal in_mono)



end 
