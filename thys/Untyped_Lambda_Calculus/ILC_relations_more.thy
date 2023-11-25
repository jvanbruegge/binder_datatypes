(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory ILC_relations_more
imports ILC_uniform ILC_affine ILC_Beta ILC_UBeta
begin


(* TO DOCUMENT IN THE PAPER: 
An example where normal induction would not work, but fresh induction with empty parameters 
is helpful -- namely, the "bonus" freshness assumption allows us to assume xs fresh for es, 
which is crucial in the beta case. *)
lemma istep_affine:
assumes "istep e e'" and "affine e"
shows "affine e'"
proof-
  have "small {}" by simp
  thus ?thesis using assms apply(induct rule: BE_induct_istep')
    subgoal for xs e1 es2 apply(rule imkSubst_affine)
    unfolding affine_iApp_iff by auto 
    subgoal unfolding affine_iApp_iff using istep_FFVars by fastforce
    subgoal unfolding affine_iApp_iff using istep_FFVars 
    by simp (smt (verit, ccfv_SIG) Int_subset_empty1 More_Stream.theN disjoint_iff snth_sset snth_supd_diff snth_supd_same)
    subgoal by auto . 
qed


(* *)

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


(* TO DOCUMENT in the paper: 
Mazza is very informal when defining \<Rightarrow> (the uniform step relation). 
One way to make this rigorous was to define reduction of a countable number of 
(i.e., a stream of) terms in parallel, and to flatten from matrix to streams when we get to 
application. (Mazza fails to discuss this 'escalation" to matrices... )
*)

lemma sset_smap2: "sset (smap2 f xs ys) = {(f (snth xs i) (snth ys i)) | i . True}"
unfolding sset_range by auto

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
    


lemma uniformS_def4: 
"uniformS es = (\<forall>e e'. {e, e'} \<subseteq> sset es \<union> sset es \<longrightarrow> reneqv e e')"
using uniformS_def3[unfolded reneqvS_def] .


lemma sset_sflat: "sset (sflat xss) = \<Union> (sset ` (sset xss))"
unfolding sset_range image_def apply (auto simp: snth_sflat) 
apply (smt (verit, ccfv_threshold) mem_Collect_eq snth2.elims) 
by (metis bij_inv_eq_iff bij_nat2 snth2.simps)


lemma uniformS_smap2_iApp_iff: 
"uniformS (smap2 iApp es ess) \<longleftrightarrow> uniformS es \<and> uniformS (sflat ess)"
unfolding uniformS_def4 sset_sflat sset_smap2 unfolding sset_range apply auto
  apply (metis iApp_inject reneqv_iApp_casesR)
  subgoal for i j i' j' apply(erule allE[of _ "iApp (es !! i) (ess !! i)"])
  apply(erule allE[of _ "iApp (es !! i') (ess !! i')"]) apply auto
  using reneqv_iApp_casesR by fastforce
  subgoal by (metis Un_iff insert_subset rangeI reneqv.iApp sset_range) .


lemma dsmap_eq: 
"inj_on f (dsset xs) \<Longrightarrow> dsmap f xs = xs \<longleftrightarrow> id_on (dsset xs) f"
sorry

lemma iLam_same_inject: "iLam (xs::ivar dstream) e = iLam xs e' \<longleftrightarrow> e = e'"
unfolding iLam_inject apply auto sorry


lemma reneqv_iLam_iff:
assumes "super xs"
shows "reneqv (iLam xs e) (iLam xs e') \<longleftrightarrow> reneqv e e'"
by (metis assms iLam_same_inject reneqv.iLam reneqv_iLam_casesR)


lemma uniformS_smap2_iLam_iff:
assumes "super xs"
shows "uniformS (smap (iLam xs) es) \<longleftrightarrow> uniformS es"
using assms unfolding uniformS_def4 by (force simp: image_def reneqv_iLam_iff) 


find_theorems uniform iLam

lemma uniformS_smap_iLam_imp: 
assumes "uniformS (smap (iLam xs) es)"
shows "\<exists>f ys. bij f \<and> |supp f| < |UNIV::ivar set| \<and> 
 super ys \<and> ys = dsmap f xs \<and> 
 smap (iLam xs) es = smap (iLam ys) (smap (irrename f) es) \<and>
 id_on (\<Union> (FFVars ` (sset es)) - dsset xs) f"
sorry

lemma ustep_uniformS:
assumes "ustep es es'" and "uniformS es"
shows "uniformS es'"
proof-
  have "small {}" by simp
  thus ?thesis using assms proof(induct rule: BE_induct_ustep')
    case (Beta es es')
    then show ?case using hred_uniformS by simp
  next
    case (iAppL es es' ess)
    then show ?case unfolding uniformS_smap2_iApp_iff by auto
  next
    case (iAppR ess ess' es)
    then show ?case unfolding uniformS_smap2_iApp_iff by auto
  next
    case (Xi es es' xs)
    from uniformS_smap_iLam_imp[OF Xi(4)]
    obtain f ys where f: "bij f" "|supp f| \<subset> |UNIV|"
    and ys: "super ys" "ys = dsmap f xs"
    and il: "smap (iLam xs) es = smap (iLam ys) (smap (irrename f) es)"
    and id: "id_on (\<Union> (ILC.FFVars ` sset es) - dsset xs) f"
    by auto
    have 0: "smap (iLam xs) es' = smap (iLam ys) (smap (irrename f) es')" sorry
    have 1: "uniformS (smap (iLam ys) (smap (irrename f) es))" using Xi(4) unfolding il .
    hence 2: "uniformS (smap (irrename f) es)" unfolding uniformS_smap2_iLam_iff[OF ys(1)] .
    
    show ?case unfolding 0

    unfolding uniformS_smap2_iLam_iff[OF ys(1)] using Xi
  qed 
    









end 
