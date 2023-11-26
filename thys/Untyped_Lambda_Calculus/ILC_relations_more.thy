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
 (\<forall>i j i' j'. affine (snth2 ess (i,j)) \<and> ILC.FFVars ((snth2 ess (i,j))) \<inter> ILC.FFVars ((snth2 ess (i,j))) = {})"
sorry 

lemma ustep_affine:
assumes "ustep es es'" and "affineS es"
shows "affineS es'"
proof-
  have "ILC2.small {} \<and> bsmall {}" by auto
  thus ?thesis using assms apply(induct rule: BE_induct_ustep')
    subgoal for es es' using hred_affineS by auto
    subgoal unfolding affineS_smap2_iApp_iff using ustep_FFVars by fastforce
    subgoal  unfolding affineS_smap2_iApp_iff using ustep_FFVars apply (auto simp: affineS_sflat) sledgehammer
    subgoal by auto . 
qed


(* *)




(* TO DOCUMENT in the paper: 
Mazza is very informal when defining \<Rightarrow> (the uniform step relation). 
One way to make this rigorous was to define reduction of a countable number of 
(i.e., a stream of) terms in parallel, and to flatten from matrix to streams when we get to 
application. (Mazza fails to discuss this 'escalation" to matrices... )
*)



(*
lemma ustep_reneqvS:
assumes "reneqvS es ees" "ustep es es'" "ustep ees ees'"
shows "reneqvS es' ees'"
proof-
  have "small {}" by simp
  thus ?thesis using assms( apply(induct rule: BE_induct_ustep')
    subgoal using hred_uniformS .
    subgoal unfolding uniformS_def3  reneqvS_def sset_smap2 apply auto  
    sledgehammer
*)
    

find_theorems uniform iLam

lemma uniformS_smap_iLam_imp: 
assumes "uniformS (smap (iLam xs) es)"
shows "\<exists>f ys. bij f \<and> |supp f| < |UNIV::ivar set| \<and> 
 super ys \<and> ys = dsmap f xs \<and> 
 smap (iLam xs) es = smap (iLam ys) (smap (irrename f) es) \<and>
 id_on (\<Union> (FFVars ` (sset es)) - dsset xs) f"
sorry











end 
