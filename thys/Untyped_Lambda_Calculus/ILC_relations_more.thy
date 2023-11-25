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
